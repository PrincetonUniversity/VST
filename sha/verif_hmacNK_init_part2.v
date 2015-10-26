Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.
Require Import sha.spec_hmacNK.
Require Import vst_lemmas.
Require Import hmac_pure_lemmas.
Require Import hmac_common_lemmas.

Require Import split_array_lemmas.

Require Import sha.hmac_NK.
Require Import sha.verif_hmacNK_init_part1.

Lemma isbyte_zeroExt8: forall x, isbyteZ x -> Int.repr x = (Int.zero_ext 8 (Int.repr x)).
Proof. intros. rewrite zero_ext_inrange. trivial.
  simpl.  unfold isbyteZ in H. rewrite Int.unsigned_repr. omega.
  split. omega. rewrite int_max_unsigned_eq. omega.
Qed. 

Lemma isbyte_zeroExt8': forall x, isbyteZ x -> x = Int.unsigned (Int.zero_ext 8 (Int.repr x)).
Proof. intros. rewrite <- isbyte_zeroExt8; trivial.
  rewrite Int.unsigned_repr; trivial. unfold isbyteZ in H. 
  split. omega. rewrite int_max_unsigned_eq. omega.
Qed. 

Lemma eval_cast_tuchar_of_isbyteZ q: isbyteZ q ->
      eval_cast tuchar tuchar (Vint (Int.repr q)) = Vint (Int.repr q). 
Proof. unfold eval_cast. simpl. intros. f_equal. apply zero_ext_inrange. simpl. 
  destruct H.
  rewrite Int.unsigned_repr. omega. rewrite int_max_unsigned_eq. omega.
Qed.

Lemma Znth_map_Vint_is_int_I8: forall l (i : Z) (F: Forall isbyteZ l),
       0 <= i < Zlength l -> 
is_int I8 Unsigned
  (Znth i (map Vint (map Int.repr l)) Vundef).
Proof. intros. unfold Znth.
if_tac; [omega | ].
assert (Z.to_nat i < length l)%nat.
destruct H.
rewrite Zlength_correct in H1.
apply Z2Nat.inj_lt in H1; try omega.
rewrite Nat2Z.id in H1. auto.
unfold is_int. simpl.
clear - H1 F.
revert l F H1; induction (Z.to_nat i); destruct l; intros; simpl in *.
omega. 
apply Forall_inv in F. specialize (isbyteZ_range _ F); intros R.
  rewrite Int.unsigned_repr. omega. split. omega.  
  assert ( Byte.max_unsigned <= Int.max_unsigned).
    unfold Byte.max_unsigned, Int.max_unsigned. 
    unfold Byte.modulus, Int.modulus, Byte.wordsize, Int.wordsize. simpl. omega.
   omega.
  omega.
 apply IHn; try omega. inversion F; trivial.
Qed.

Lemma Znth_map_Vint_is_int_I8': forall l (i : Z) ,
       0 <= i < Zlength l -> 
is_int I8 Unsigned
  (Znth i (map Vint (map Int.repr (map Byte.unsigned l))) Vundef).
Proof. intros. apply Znth_map_Vint_is_int_I8.
  apply isbyte_map_ByteUnsigned.
  rewrite Zlength_map; trivial.
Qed.

Lemma UPD_IPAD: forall
  (key : list Z)
  (ZLI : Zlength
        (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad) =
      64)
  (i : Z)
  (I : 0 <= i < 64)
  (isbyteZQb : isbyteZ (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0))
  (X : Znth i (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) Vundef =
      Vint (Int.repr (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0))),
upd_Znth_in_list i
  (sublist 0 i
     (map Vint
        (map Int.repr
           (map Byte.unsigned
              (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)))) ++
   sublist i 64 (default_val (Tarray tuchar 64 noattr)))
  (Vint
     (Int.zero_ext 8
        (Int.repr (Z.lxor (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0) 54)))) =
sublist 0 (i + 1)
  (map Vint
     (map Int.repr
        (map Byte.unsigned
           (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)))) ++
sublist (i + 1) 64 (default_val (Tarray tuchar 64 noattr)).
Proof. intros. unfold HMAC_SHA256.mkArgZ in *.
  rewrite upd_Znth_in_list_app2, Zlength_sublist, Zminus_0_r, Zminus_diag,
     upd_Znth_in_list0; repeat rewrite Zlength_sublist; try omega.
  2: rewrite Zlength_default_val_Tarray_tuchar; omega. 
  2: do 2 rewrite Zlength_map; rewrite ZLI; omega.
  2: rewrite Zlength_default_val_Tarray_tuchar; omega. 
  2: do 2 rewrite Zlength_map; rewrite ZLI; omega.
  rewrite <- (sublist_rejoin 0 i (i+1)); try omega.
  2: do 2 rewrite Zlength_map; rewrite ZLI; omega.
  rewrite <- app_assoc. f_equal.
  rewrite (sublist_singleton i) with (d:=Vint (Int.zero)); simpl app.
  2: do 2 rewrite Zlength_map; rewrite ZLI; omega.
  f_equal. rewrite Znth_map with (d':=Int.zero). f_equal.
           rewrite Znth_map with (d':=Z0). 
           rewrite Znth_map with (d':=Byte.zero). unfold HMAC_SHA256.mkArg.
           unfold Znth. unfold Znth in X. destruct (zlt i 0). discriminate.
           specialize (map_nth (fun p : byte * byte => Byte.xor (fst p) (snd p))
                                       (combine (map Byte.repr (HMAC_SHA256.mkKey key)) (HMAC_SHA256.sixtyfour Ipad)) 
                                       (Byte.zero, Byte.zero)
                                       (Z.to_nat i)). simpl. 
           rewrite Byte.xor_zero; intros MN; rewrite MN; clear MN.
                   rewrite combine_nth. 
                   Focus 2. rewrite map_length, length_SF, mkKey_length. reflexivity.
                   assert (BMU: Byte.max_unsigned = 255). reflexivity.
                   assert (isByte54: 0 <= 54 <= Byte.max_unsigned).
                      rewrite BMU; omega. 
                   destruct (isbyteZ_xor (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0) 54 isbyteZQb) as [AA BB].
                     split; rewrite BMU in *; omega.
                   remember (HMAC_SHA256.sixtyfour Ipad).  simpl.
                   rewrite (map_nth Byte.repr (HMAC_SHA256.mkKey key) Z0).
                   unfold Byte.xor.
                   assert (NTH: nth (Z.to_nat i) l Byte.zero = Byte.repr 54).
                     subst l. apply nth_list_repeat'. apply (Z2Nat.inj_lt _ 64). apply I. omega. omega.
                   rewrite NTH, (Byte.unsigned_repr 54); trivial.
                   rewrite (Byte.unsigned_repr (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0)).
                     Focus 2. destruct isbyteZQb. omega.
                   rewrite Byte.unsigned_repr.
                   apply zero_ext_inrange.
                   rewrite Int.unsigned_repr.
                   assert (Z.lxor (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0) 54 < two_p 8 ). apply BB. omega.
                   rewrite int_max_unsigned_eq.
                   intuition.
                   omega.
                   rewrite Zlength_map in ZLI; rewrite ZLI; assumption.
                   rewrite ZLI; assumption.
                   rewrite Zlength_map, ZLI; assumption.
  rewrite sublist_sublist; try omega.
  assert (64 - i + i = 64) by omega. rewrite Zplus_comm, H; trivial.
Qed.

Lemma UPD_OPAD: forall
  (key : list Z)
  (ZLI : Zlength (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad) = 64)
  (ZLO : Zlength (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad) = 64)
  (i : Z)
  (I : 0 <= i < 64)
  (isbyteZQb : isbyteZ (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0))
  (X : Znth i (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) Vundef =
       Vint (Int.repr (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0))),upd_Znth_in_list i
  (sublist 0 i
     (map Vint
        (map Int.repr
           (map Byte.unsigned
              (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Opad)))) ++
   sublist i 64
     (map Vint
        (map Int.repr
           (map Byte.unsigned
              (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)))))
  (Vint
     (Int.zero_ext 8
        (Int.xor (Int.repr 92)
           (Int.zero_ext 8
              (Int.repr (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0)))))) =
sublist 0 (i + 1)
  (map Vint
     (map Int.repr
        (map Byte.unsigned
           (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Opad)))) ++
sublist (i + 1) 64
  (map Vint
     (map Int.repr
        (map Byte.unsigned
           (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)))).
Proof. intros. unfold HMAC_SHA256.mkArgZ in *.
  rewrite upd_Znth_in_list_app2, Zlength_sublist, Zminus_0_r, Zminus_diag,
     upd_Znth_in_list0; repeat rewrite Zlength_sublist; try omega.
  2: do 2 rewrite Zlength_map; rewrite ZLI; omega.
  2: do 2 rewrite Zlength_map; rewrite ZLO; omega.
  2: do 2 rewrite Zlength_map; rewrite ZLI; omega.
  2: do 2 rewrite Zlength_map; rewrite ZLO; omega.
  rewrite <- (sublist_rejoin 0 i (i+1)); try omega.
  2: do 2 rewrite Zlength_map; rewrite ZLO; omega.
  rewrite <- app_assoc. f_equal.
  rewrite (sublist_singleton i) with (d:=Vint (Int.zero)); simpl app.
  2: do 2 rewrite Zlength_map; rewrite ZLO; omega.
  f_equal. rewrite Znth_map with (d':=Int.zero). f_equal.
           rewrite Znth_map with (d':=Z0). 
           rewrite Znth_map with (d':=Byte.zero). unfold HMAC_SHA256.mkArg.
           unfold Znth. unfold Znth in X. destruct (zlt i 0). discriminate.
           specialize (map_nth (fun p : byte * byte => Byte.xor (fst p) (snd p))
                                       (combine (map Byte.repr (HMAC_SHA256.mkKey key)) (HMAC_SHA256.sixtyfour Opad)) 
                                       (Byte.zero, Byte.zero)
                                       (Z.to_nat i)). simpl. 
           rewrite Byte.xor_zero; intros MN; rewrite MN; clear MN.
                   rewrite combine_nth. 
                   Focus 2. rewrite map_length, length_SF, mkKey_length. reflexivity.
                   assert (BMU: Byte.max_unsigned = 255). reflexivity.
                   rewrite Int.xor_commut.
                   assert (isByte92: 0 <= 92 <= Byte.max_unsigned).
                      rewrite BMU; omega. 
                   destruct (isbyteZ_xor (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0) 92 isbyteZQb) as [AA BB].
                     split; rewrite BMU in *; omega.
                   remember (HMAC_SHA256.sixtyfour Opad).  simpl.
                   rewrite (map_nth Byte.repr (HMAC_SHA256.mkKey key) Z0).
                   unfold Byte.xor.
                   assert (NTH: nth (Z.to_nat i) l Byte.zero = Byte.repr 92).
                     subst l. apply nth_list_repeat'. apply (Z2Nat.inj_lt _ 64). apply I. omega. omega.
                   rewrite NTH, (Byte.unsigned_repr 92); trivial.
                   rewrite (Byte.unsigned_repr (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0)).
                     Focus 2. destruct isbyteZQb. omega.
                   rewrite Byte.unsigned_repr. unfold Int.xor.
                   rewrite Int.unsigned_repr.  
                   rewrite <- isbyte_zeroExt8; trivial.
                   rewrite zero_ext_inrange.
                   rewrite Int.unsigned_repr; trivial.
                   destruct isbyteZQb. rewrite int_max_unsigned_eq; split; omega.
                   rewrite Int.unsigned_repr.
                   destruct isbyteZQb. simpl. omega.
                   destruct isbyteZQb. rewrite int_max_unsigned_eq; split; omega.
                   rewrite zero_ext_inrange.
                   rewrite Int.unsigned_repr.
                   split; assumption. 
                   destruct isbyteZQb. rewrite int_max_unsigned_eq; split; omega.
                   rewrite Int.unsigned_repr. simpl. destruct isbyteZQb. omega.
                   destruct isbyteZQb. rewrite int_max_unsigned_eq; split; omega.
                   rewrite int_max_unsigned_eq; omega.
                   omega.
                   rewrite Zlength_map in ZLO; rewrite ZLO; assumption.
                   rewrite ZLO; assumption.
                   rewrite Zlength_map, ZLO; assumption.
  rewrite sublist_sublist; try omega.
  assert (64 - i + i = 64) by omega. rewrite Zplus_comm, H; trivial.
Qed.

(*Definition postResetHMS (iS oS: s256state): hmacstate :=
  (emptySha, (iS, oS)).*)
Definition postResetHMS (iS oS: s256state): hmacstate :=
  (default_val t_struct_SHA256state_st, (iS, oS)).

Definition initPostResetConditional r (c:val) (k: val) h key iS oS: mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0 then hmacstate_PreInitNull key h c else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF
                  else !!(Forall isbyteZ key) &&
                       ((data_at Tsh t_struct_hmac_ctx_st (postResetHMS iS oS) c) *
                        (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr b ofs)))
  | _ => FF
  end.

Lemma ipad_loop Espec pb pofs cb cofs ckb ckoff kb kofs l key kv
(HMS' : reptype t_struct_hmac_ctx_st) (FR:mpred): forall
(KL1 : l = Zlength key)
(KL2 : 0 < l <= Int.max_signed)
(KL3 : l * 8 < two_p 64)
(KHMS : HMS' = HMS)
(IPADcont : list val)
(HeqIPADcont : IPADcont =
              map Vint
                (map Int.repr
                   (map Byte.unsigned
                      (HMAC_SHA256.mkArg
                         (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad))))
(ZLI : Zlength
        (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad) =
      64)
(isbyte_key : Forall isbyteZ key),
@semax CompSpecs Espec
  (initialized _reset (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs))
  (PROP  ()
   LOCAL  (temp _reset (Vint (Int.repr 1));
   lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
   lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
   temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
   temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
   SEP  ( (*`(K_vector kv);*) `(FR);
   `(data_at Tsh (Tarray tuchar 64 noattr)
       (default_val (Tarray tuchar 64 noattr)) (Vptr pb pofs));
   (*`(data_at Tsh t_struct_hmac_ctx_st HMS' (Vptr cb cofs));*)
   `(data_at Tsh (tarray tuchar 64)
       (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff)) (*;
   `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
       (Vptr kb kofs))*)))
  (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 64) tint) tint)
     (Ssequence
        (Sset _aux
           (Ecast
              (Ederef
                 (Ebinop Oadd (Evar _ctx_key (Tarray tuchar 64 noattr))
                    (Etempvar _i tint) (tptr tuchar)) tuchar) tuchar))
        (Ssequence
           (Sset _aux
              (Ecast
                 (Ebinop Oxor (Econst_int (Int.repr 54) tint)
                    (Etempvar _aux tuchar) tint) tuchar))
           (Sassign
              (Ederef
                 (Ebinop Oadd (Evar _pad (Tarray tuchar 64 noattr))
                    (Etempvar _i tint) (tptr tuchar)) tuchar)
              (Etempvar _aux tuchar))))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))
  (normal_ret_assert
     (PROP  ()
      LOCAL  (temp _reset (Vint (Int.repr 1));
      lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
      lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
      temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
      temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
      SEP  ((*`(K_vector kv);*) `(FR);
      `(data_at Tsh (Tarray tuchar 64 noattr) IPADcont (Vptr pb pofs));
(*      `(data_at Tsh t_struct_hmac_ctx_st HMS' (Vptr cb cofs));*)
      `(data_at Tsh (tarray tuchar 64)
          (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff)) (*;
      `(data_at Tsh (tarray tuchar (Zlength key))
          (map Vint (map Int.repr key)) (Vptr kb kofs))*)))).
Proof. intros. abbreviate_semax.   
eapply semax_post'.
Focus 2.   
      forward_for_simple_bound' 64 (EX i:Z, 
        (PROP  ()
         LOCAL  (temp _reset (Vint (Int.repr 1));
           lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
           lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
           temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
           temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
         SEP  ((*`(K_vector kv);*) `(FR);
          `(data_at Tsh (Tarray tuchar 64 noattr) 
             ((sublist 0 i IPADcont) ++ (sublist i 64  (default_val (Tarray tuchar 64 noattr))))
             (Vptr pb pofs));
(*          `(data_at Tsh t_struct_hmac_ctx_st (*keyedHMS*)HMS' (Vptr cb cofs));*)
          `(data_at Tsh (tarray tuchar 64)
              (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff)) (*;
         `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
              (Vptr kb kofs))*)))).
      { (*precondition implies "invariant"*)
        rewrite sublist_nil, sublist_same; trivial. simpl app.
        entailer.  
      }
      { rename H into I. 
        assert (Xb: exists qb, nth (Z.to_nat i) (HMAC_SHA256.mkKey key) Z0 = qb /\ isbyteZ qb).
          { destruct (nth_mapIn (Z.to_nat i) (HMAC_SHA256.mkKey key) 0) as [? [? ?]].
             rewrite mkKey_length.
              split. apply (Z2Nat.inj_le 0); omega. apply (Z2Nat.inj_lt _ 64); omega.
            exists x; split; trivial. eapply Forall_forall. apply isbyteZ_mkKey. eassumption. eassumption.
          }
        destruct Xb as [qb [Qb isbyteZQb]].
        assert (X: Znth i (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) Vundef
                   = Vint (Int.repr qb)). (* (Int.zero_ext 8 q)).*)
          { unfold Znth. destruct (zlt i 0). omega.
            rewrite nth_indep with (d':=Vint (Int.repr 0)).
              Focus 2. repeat rewrite map_length. rewrite mkKey_length. unfold SHA256.BlockSize; simpl. apply (Z2Nat.inj_lt _ 64); omega. 
            repeat rewrite map_nth. rewrite Qb. trivial. 
          }
        forward. entailer.

        apply prop_right. rewrite X. simpl. rewrite <- isbyte_zeroExt8'; trivial.
               apply (isbyteZ_range _ isbyteZQb). 
        rewrite X.
        forward. 
        unfold Int.xor. 
        rewrite Int.unsigned_repr. 2: rewrite int_max_unsigned_eq; omega.
        (*rewrite Int.unsigned_repr. 2: destruct isbyteZQb; rewrite int_max_unsigned_eq; omega.*)
        exploit (isbyteZ_xor 54 qb); trivial. split; omega.
        intros isbyteXOR.
        rewrite <- (isbyte_zeroExt8 qb); trivial.
        rewrite Int.unsigned_repr. 2: destruct isbyteZQb; rewrite int_max_unsigned_eq; omega.
        rewrite Z.lxor_comm. remember (Vint (Int.repr (Z.lxor qb 54))) as xorval.
        forward. entailer!.
        rewrite field_at_data_at. 
        apply derives_refl'. f_equal. apply UPD_IPAD; assumption. 
        unfold field_address; simpl. rewrite if_true, Int.add_zero; trivial. (*Issue: we're (forced to?) unfolding field_address too often*)
      }
Unfocus.
cbv beta. rewrite sublist_same, sublist_nil, app_nil_r; trivial. entailer.
subst IPADcont; do 2 rewrite Zlength_map. 
unfold HMAC_SHA256.mkArgZ in ZLI; rewrite ZLI; trivial.
Qed. 

Definition FRAME1 cb cofs ckb ckoff kb kofs key (HMS': reptype t_struct_hmac_ctx_st) := 
    (field_at Tsh t_struct_hmac_ctx_st [StructField 13%positive] (fst HMS')
        (Vptr cb cofs)) *
    (field_at Tsh t_struct_hmac_ctx_st [StructField 15%positive]
         (snd (snd HMS')) (Vptr cb cofs)) *
    (data_at Tsh (tarray tuchar 64)
          (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff)) *
    (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
        (Vptr kb kofs)).
Definition FRAME2 kb kofs cb cofs kv key ipadSHAabs 
                (HMS' : reptype t_struct_hmac_ctx_st) := (K_vector kv) * 
   (sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108)))) *
   (field_at Tsh t_struct_hmac_ctx_st [StructField 13%positive] (fst HMS')
       (Vptr cb cofs)) *
   (field_at Tsh t_struct_hmac_ctx_st [StructField 15%positive]
       (snd (snd HMS')) (Vptr cb cofs)) * 
   ( data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
       (Vptr kb kofs)). 

Opaque FRAME1. Opaque FRAME2.

Lemma opadloop Espec pb pofs cb cofs ckb ckoff kb kofs l key kv 
(HMS' : reptype t_struct_hmac_ctx_st): forall
(KL1 : l = Zlength key)
(KL2 : 0 < l <= Int.max_signed)
(KL3 : l * 8 < two_p 64)
(KHMS : HMS' = HMS)
(h1 : hmacabs)
(IPADcont : list val)
(HeqIPADcont : IPADcont =
              map Vint
                (map Int.repr
                   (map Byte.unsigned
                      (HMAC_SHA256.mkArg
                         (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad))))
(OPADcont : list val)
(HeqOPADcont : OPADcont =
              map Vint
                (map Int.repr
                   (map Byte.unsigned
                      (HMAC_SHA256.mkArg
                         (map Byte.repr (HMAC_SHA256.mkKey key)) Opad))))
(ZLI : Zlength
        (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad) = 64)
(ZLO : Zlength
        (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad) = 64)
(isbyte_key : Forall isbyteZ key)
(*Delta := abbreviate : tycontext*)
(ipadSHAabs : s256abs),
@semax CompSpecs Espec
  (initialized_list [_reset; _i] (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs))
  (PROP  ()
   LOCAL  (temp _reset (Vint (Int.repr 1));
   lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
   lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
   temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
   temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
   SEP  (`(K_vector kv);
   `(sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108))));
   `(data_block Tsh
       (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)
       (Vptr pb pofs)); `(FRAME1 cb cofs ckb ckoff kb kofs key HMS')))
  (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 64) tint) tint)
     (Ssequence
        (Sset _aux
           (Ecast
              (Ederef
                 (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                    (Etempvar _i tint) (tptr tuchar)) tuchar) tuchar))
        (Sassign
           (Ederef
              (Ebinop Oadd (Evar _pad (tarray tuchar 64)) (Etempvar _i tint)
                 (tptr tuchar)) tuchar)
           (Ebinop Oxor (Econst_int (Int.repr 92) tint)
              (Etempvar _aux tuchar) tint)))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))
  (normal_ret_assert 
     (PROP ()
      LOCAL (temp _reset (Vint (Int.repr 1));
             lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
             lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs); temp _ctx (Vptr cb cofs);
             temp _key (Vptr kb kofs); temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
      SEP  (`(K_vector kv);
            `(sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108))));
            `(data_at Tsh (Tarray tuchar 64 noattr) OPADcont (Vptr pb pofs));
            `(FRAME1 cb cofs ckb ckoff kb kofs key HMS')))).
Proof. intros. abbreviate_semax. 
eapply semax_post'.
Focus 2.   
      forward_for_simple_bound' 64 (EX i:Z, 
        (PROP  ()
         LOCAL  (temp _reset (Vint (Int.repr 1));
            lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
            lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
            temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
            temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
         SEP  (`(K_vector kv); `(sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108))));
          `(data_at Tsh (Tarray tuchar 64 noattr) 
              ((sublist 0 i OPADcont) ++ (sublist i 64 IPADcont)) (Vptr pb pofs));
          `(FRAME1 cb cofs ckb ckoff kb kofs key HMS')))).
      { (*precondition implies "invariant"*)
        unfold data_block.
        rewrite sublist_nil, sublist_same; trivial.
          simpl app. entailer. cancel. rewrite ZLI. unfold tarray, HMAC_SHA256.mkArgZ. trivial.
        subst IPADcont. do 2 rewrite Zlength_map. unfold HMAC_SHA256.mkArgZ in ZLI; rewrite ZLI. trivial. 
      } 
      { rename H into I. 
        assert (Xb: exists qb, nth (Z.to_nat i) (HMAC_SHA256.mkKey key) Z0 = qb /\ isbyteZ qb).
          { destruct (nth_mapIn (Z.to_nat i) (HMAC_SHA256.mkKey key) 0) as [? [? ?]].
             rewrite mkKey_length.
              split. apply (Z2Nat.inj_le 0); omega. apply (Z2Nat.inj_lt _ 64); omega.
            exists x; split; trivial. eapply Forall_forall. apply isbyteZ_mkKey. eassumption. eassumption.
          }
        destruct Xb as [qb [Qb isbyteZQb]].
        assert (X: Znth i (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) Vundef
                   = Vint (Int.repr qb)). (* (Int.zero_ext 8 q)).*)
          { unfold Znth. destruct (zlt i 0). omega.
            rewrite nth_indep with (d':=Vint (Int.repr 0)).
              Focus 2. repeat rewrite map_length. rewrite mkKey_length. unfold SHA256.BlockSize; simpl. apply (Z2Nat.inj_lt _ 64); omega. 
            repeat rewrite map_nth. rewrite Qb. trivial. 
          }

        gather_SEP 0 1 2 3. 
        replace_SEP 0 (`(FRAME2 kb kofs cb cofs kv key ipadSHAabs HMS') *
                       `(data_at Tsh (Tarray tuchar 64 noattr)
                           (sublist 0 i OPADcont ++ sublist i 64 IPADcont) (Vptr pb pofs)) *
                       `(data_at Tsh (tarray tuchar 64)
                           (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff))).
        { entailer. Transparent FRAME1. Transparent FRAME2. Transparent default_val.
            unfold FRAME1, FRAME2, HMS, default_val. simpl. cancel.
        } Opaque FRAME1. Opaque FRAME2. 
        normalize.
        forward. Opaque default_val. (*Issue : forward succeeds in 3secs, but if 
              we put the Opaque declaration before the forward (next to Opaque FRAME2, as one would expect),
              the forward leads to memory exhaustion. *)
        { entailer.
          apply prop_right. rewrite X. simpl. rewrite <- isbyte_zeroExt8'; trivial.
                apply (isbyteZ_range _ isbyteZQb). 
        }
        rewrite X.
        forward.
        entailer!. rewrite field_at_data_at. 
        Transparent FRAME1. Transparent FRAME2. Transparent default_val.
            unfold FRAME1, FRAME2, HMS, default_val. simpl. cancel.
        apply derives_refl'. f_equal. apply UPD_OPAD; eassumption.
        unfold field_address; simpl. rewrite if_true, Int.add_zero; trivial.
      }
Unfocus.
cbv beta. rewrite sublist_same, sublist_nil, app_nil_r; trivial. entailer!.
subst OPADcont; do 2 rewrite Zlength_map. 
unfold HMAC_SHA256.mkArgZ in ZLO; rewrite ZLO; trivial.
Qed. 

Opaque FRAME1. Opaque FRAME2.

Lemma init_part2: forall
(Espec : OracleKind)
(c : val)
(k : val)
(l : Z)
(key : list Z)
(kv : val)
(h1 : hmacabs)
(KL1 : l = Zlength key)
(KL2 : 0 < l <= Int.max_signed)
(KL3 : l * 8 < two_p 64)
(ctx' : name _ctx)
(key' : name _key)
(len' : name _len)
(*(Delta := initialized _reset 
       (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs))*)
(cb : block)
(cofs : int)
(pad : val)
(r : Z)
(ckb : block)
(ckoff : int)
(*(HC : c = Vptr cb cofs)*)
(R : r = 0 \/ r = 1)
(PostResetBranch : environ -> mpred)
(HeqPostResetBranch : PostResetBranch = EX shaStates:_ ,
          PROP  (innerShaInit (map Byte.repr (HMAC_SHA256.mkKey key))
                           (fst shaStates) /\
                  s256_relate (fst shaStates) (fst (snd shaStates)) /\
                  outerShaInit (map Byte.repr (HMAC_SHA256.mkKey key))
                           (fst (snd (snd shaStates))) /\ 
                  s256_relate (fst (snd (snd shaStates))) (snd (snd (snd shaStates))))
          LOCAL  (lvar _pad (tarray tuchar 64) pad; 
                  lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff); 
                  temp _ctx (Vptr cb cofs); temp _key k;
                  temp _len (Vint (Int.repr l));
                  gvar sha._K256 kv)
          SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                `(data_at_ Tsh (Tarray tuchar 64 noattr) (Vptr ckb ckoff)); 
                `(initPostResetConditional r (Vptr cb cofs) k h1 key (fst (snd shaStates)) (snd (snd (snd shaStates))));
                `(K_vector kv))),
@semax CompSpecs Espec (*Delta*) (initialized _reset 
       (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs))
  (PROP  ()
   LOCAL  (temp _reset (Vint (Int.repr r));
   lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff); lvar _pad (tarray tuchar 64) pad;
   temp _ctx (Vptr cb cofs); temp _key k; temp _len (Vint (Int.repr l));
   gvar sha._K256 kv)
   SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
   `(initPostKeyNullConditional r (Vptr cb cofs) k h1 key (Vptr ckb ckoff));
   `(K_vector kv)))
  (Sifthenelse (Etempvar _reset tint)
     (Ssequence
        (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
           (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 64) tint)
              tint)
           (Ssequence
              (Sset _aux
                 (Ecast
                    (Ederef
                       (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                          (Etempvar _i tint) (tptr tuchar)) tuchar) tuchar))
              (Ssequence
                 (Sset _aux
                    (Ecast
                       (Ebinop Oxor (Econst_int (Int.repr 54) tint)
                          (Etempvar _aux tuchar) tint) tuchar))
                 (Sassign
                    (Ederef
                       (Ebinop Oadd (Evar _pad (tarray tuchar 64))
                          (Etempvar _i tint) (tptr tuchar)) tuchar)
                    (Etempvar _aux tuchar))))
           (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                 tint)))
        (Ssequence
           (Scall None
              (Evar _SHA256_Init
                 (Tfunction (Tcons (tptr t_struct_SHA256state_st) Tnil) tvoid
                    cc_default))
              [Eaddrof
                 (Efield
                    (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                       t_struct_hmac_ctx_st) _i_ctx t_struct_SHA256state_st)
                 (tptr t_struct_SHA256state_st)])
           (Ssequence
              (Scall None
                 (Evar _SHA256_Update
                    (Tfunction
                       (Tcons (tptr t_struct_SHA256state_st)
                          (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                       cc_default))
                 [Eaddrof
                    (Efield
                       (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                          t_struct_hmac_ctx_st) _i_ctx
                       t_struct_SHA256state_st)
                    (tptr t_struct_SHA256state_st);
                 Evar _pad (tarray tuchar 64); Econst_int (Int.repr 64) tint])
              (Ssequence
                 (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
                    (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 64) tint) tint)
                    (Ssequence
                       (Sset _aux
                          (Ecast
                             (Ederef
                                (Ebinop Oadd
                                   (Evar _ctx_key (tarray tuchar 64))
                                   (Etempvar _i tint) (tptr tuchar)) tuchar)
                             tuchar))
                       (Sassign
                          (Ederef
                             (Ebinop Oadd (Evar _pad (tarray tuchar 64))
                                (Etempvar _i tint) (tptr tuchar)) tuchar)
                          (Ebinop Oxor (Econst_int (Int.repr 92) tint)
                             (Etempvar _aux tuchar) tint)))
                    (Sset _i
                       (Ebinop Oadd (Etempvar _i tint)
                          (Econst_int (Int.repr 1) tint) tint)))
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
                                t_struct_hmac_ctx_st) _o_ctx
                             t_struct_SHA256state_st)
                          (tptr t_struct_SHA256state_st)])
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
                                t_struct_hmac_ctx_st) _o_ctx
                             t_struct_SHA256state_st)
                          (tptr t_struct_SHA256state_st);
                       Evar _pad (tarray tuchar 64);
                       Econst_int (Int.repr 64) tint])))))) Sskip)
    (overridePost PostResetBranch
     (frame_ret_assert
         (function_body_ret_assert tvoid
            (EX  h : hmacabs,
             PROP  (hmacInit key h)
             LOCAL ()
             SEP  (`(hmacstate_ h (Vptr cb cofs)); `(initPostKey k key);
             `(K_vector kv))))
         ((EX  v : val,
           local (lvar _pad (tarray tuchar 64) v) &&
           `(data_at_ Tsh (tarray tuchar 64) v)) *
          (EX  v : val,
           local (lvar _ctx_key (tarray tuchar 64) v) &&
           `(data_at_ Tsh (tarray tuchar 64) v))))).
Proof. intros. abbreviate_semax.
    (* Issue: Potential Coq (8.4?) bug about type equalities*)
    assert (HH: exists HMS': reptype t_struct_hmac_ctx_st, HMS'=HMS). exists HMS; reflexivity.
    destruct HH as [HMS' KHMS].
forward_if PostResetBranch. 
  { (* THEN*)
    rename H into r_true. 
    remember (map Vint (map Int.repr 
              (map Byte.unsigned (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)))) as IPADcont.
    remember (map Vint (map Int.repr 
              (map Byte.unsigned (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Opad)))) as OPADcont.
    assert (ZLI: Zlength (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad) = 64).
            rewrite Zlength_mkArgZ.
            repeat rewrite map_length. rewrite mkKey_length.
            unfold SHA256.BlockSize; simpl. trivial. 
    assert (ZLO: Zlength (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad) = 64).
            rewrite Zlength_mkArgZ.
            repeat rewrite map_length. rewrite mkKey_length.
            unfold SHA256.BlockSize; simpl. trivial. 
    unfold data_at_, tarray.
    assert_PROP (isptr pad). entailer. apply isptrD in H; destruct H as [pb [pofs Hpad]]. subst pad. 
    apply semax_pre with (P':=PROP  (r<>0 /\ Forall isbyteZ key)
         LOCAL  (temp _reset (Vint (Int.repr r));
            lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
            lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
            temp _ctx (Vptr cb cofs); temp _key k; temp _len (Vint (Int.repr l));
            gvar sha._K256 kv)
         SEP  (`(K_vector kv);
               `(data_at Tsh (Tarray tuchar 64 noattr)
                   (default_val (Tarray tuchar 64 noattr)) (Vptr pb pofs));
               `(data_at Tsh t_struct_hmac_ctx_st (*keyedHMS*)HMS' (Vptr cb cofs));
               `(data_at Tsh (tarray tuchar 64) (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))
                  (Vptr ckb ckoff));
               `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) k))).
    { clear POSTCONDITION HeqPostResetBranch PostResetBranch.
      unfold initPostKeyNullConditional. entailer.
      destruct key'; try contradiction.
      (*integer, ie key==NULL*)
          simpl in TC. subst i. simpl. if_tac. subst r. inversion r_true.
          apply andp_right. entailer. entailer.
      (*key == Vptr*)
       if_tac. subst r. inversion r_true.
          entailer. cancel.
    }
    normalize. destruct R; subst r. omega. clear H. rename H0 into isbyte_key.
    assert_PROP (isptr k). entailer. apply isptrD in H; destruct H as [kb [kofs HK]]. 
    rewrite HK in *. 

    eapply semax_seq'. (*TODO: using forward_seq here introduces another Delta0 in goal2 - but it worked fine before I split this off into file XXX_part2.v *)
    instantiate (1:= 
  (PROP  ()
   LOCAL  (temp _reset (Vint (Int.repr 1));
      lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
      lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
      temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
      temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
   SEP  (`(K_vector kv);
     `(data_at Tsh (Tarray tuchar 64 noattr) IPADcont (Vptr pb pofs));
     `(data_at Tsh t_struct_hmac_ctx_st (*keyedHMS*)HMS' (Vptr cb cofs));
     `(data_at Tsh (tarray tuchar 64)
         (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff));
     `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
         (Vptr kb kofs))))).
    { (*ipad loop*)
      (*semax_subcommand HmacVarSpecs HmacFunSpecs f_HMAC_Init.*)
      eapply semax_pre_post.
      Focus 3. eapply (ipad_loop Espec pb pofs cb cofs ckb ckoff kb kofs l key kv HMS' 
                         (K_vector kv * data_at Tsh t_struct_hmac_ctx_st HMS' (Vptr cb cofs)
                          * data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
                         (Vptr kb kofs))); try eassumption.
      apply andp_left2. entailer. cancel.
      intros ? ?. apply andp_left2. apply assert_lemmas.normal_ret_assert_derives'.
                  entailer. cancel.
    }

    (*continuation after ipad-loop*) 
    assert_PROP (field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs)) as FC_C by entailer.
    unfold data_at at 2. unfold_field_at 1%nat. normalize.

    gather_SEP 0 2 5 6.
    replace_SEP 0 (`(FRAME1 cb cofs ckb ckoff kb kofs key HMS')).
    { subst HMS'. Transparent default_val. Transparent FRAME1. 
         unfold HMS, FRAME1, default_val. entailer. (*Issue: again unfold default_val here is the key *)
    }
Opaque FRAME1. Opaque default_val.
    rewrite (field_at_data_at  Tsh t_struct_hmac_ctx_st [StructField 14%positive]). (*ie i_ctx*)
    assert_PROP (field_compatible t_struct_hmac_ctx_st [StructField 14%positive] (Vptr cb cofs)) as FC_ICTX.
    { apply prop_right. clear - FC_C. red in FC_C; red; intuition. split; trivial. right; left; trivial. }
    unfold field_address; simpl. rewrite if_true; trivial. unfold field_offset, fieldlist.field_offset2; simpl.

    (*Call to _SHA256_Init*)
    unfold field_type; simpl. 
    rewrite KHMS at 2. (*Issue: note: don't rewrite in the FRAME1-erm*)
    Transparent default_val. unfold HMS, default_val; simpl. Opaque default_val.
    forward_call (Vptr cb (Int.add cofs (Int.repr 108))). 

    (*Call to _SHA256_Update*)
    forward_call (init_s256abs, 
                  HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad,
                  Vptr cb (Int.add cofs (Int.repr 108)), Vptr pb pofs, Tsh, 64, kv)
               ipadSHAabs.
    { unfold data_block. rewrite ZLI, HeqIPADcont. unfold HMAC_SHA256.mkArgZ. 
      (* Issue: entailer.Anomaly: undefined_evars_of_term: evar not found. Please report.*)
      assert (FR : Frame = [FRAME1 cb cofs ckb ckoff kb kofs key HMS']).
        subst Frame; reflexivity.
      rewrite FR; clear FR Frame. 
      simpl. normalize. apply andp_right. apply prop_right. apply isbyte_map_ByteUnsigned. cancel. 
    } 
    { clear Frame HeqPostResetBranch HeqOPADcont; subst IPADcont.
        rewrite Zlength_mkArgZ. repeat rewrite map_length. rewrite mkKey_length. intuition. 
    }
    rename H into ipadAbs_def.
    normalize.
    rewrite sublist_same in ipadAbs_def; try rewrite ZLI; trivial.

    (*essentially the same for opad*)
    eapply semax_seq'. (* TODO: using forward_seq here introduces another Delta0 in goal2 - but 
                          it worked fine before I split this off into file XXX_part2.v *)
    instantiate (1:= PROP  ()
       LOCAL  (temp _reset (Vint (Int.repr 1));
               lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
               lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs); temp _ctx (Vptr cb cofs);
               temp _key (Vptr kb kofs); temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
       SEP  (`(K_vector kv);
             `(sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108))));
             `(data_at Tsh (Tarray tuchar 64 noattr) OPADcont (Vptr pb pofs));
             `(FRAME1 cb cofs ckb ckoff kb kofs key HMS'))). 
    { (*opad loop*)
      eapply semax_pre_post.
      Focus 3. eapply (opadloop Espec pb pofs cb cofs ckb ckoff kb kofs l key kv HMS');
               try eassumption. 
      apply andp_left2. apply derives_refl.
      intros ? ?. apply andp_left2. apply derives_refl.
    }

    (*continuation after opad-loop*) 
    Transparent FRAME1. unfold FRAME1. 
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField 15%positive]).
    assert_PROP (field_compatible t_struct_hmac_ctx_st [StructField 15%positive] (Vptr cb cofs)) as FC_OCTX.
    { apply prop_right. clear - FC_C. red in FC_C; red; intuition. split; trivial. right; right; left; trivial. }
    unfold field_address; simpl. rewrite if_true; trivial. unfold field_offset, fieldlist.field_offset2; simpl.

    (*Call to _SHA256_Init*)
    unfold field_type; simpl. Transparent default_val. normalize. Opaque default_val.
    gather_SEP 0 2 3 5. 
Definition FRAME3 (kb cb ckb: block) kofs cofs ckoff key ipadSHAabs (HMS' : reptype t_struct_hmac_ctx_st):= 
       (field_at Tsh t_struct_hmac_ctx_st [StructField 13%positive] (fst HMS') (Vptr cb cofs) ) * 
       (data_at Tsh (tarray tuchar 64) (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff)) *
       (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr kb kofs)) *
       (sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108)))).
    replace_SEP 0 (`(FRAME3 kb cb ckb kofs cofs ckoff key ipadSHAabs HMS')).
    { Transparent default_val. rewrite KHMS. entailer!. }  (*Don't use entailer here!!*)
    (*TODO: one of the most recent changes in floyd (or elsewhere?) meant
    that I have to do the following unfold here t get forward_call' to apply*)
    unfold MORE_COMMANDS, abbreviate.
    (*This line is crucial: *) rewrite KHMS. unfold HMS; simpl.
    forward_call (Vptr cb (Int.add cofs (Int.repr 216))).
 
    (* Call to sha_update*)
    forward_call (init_s256abs, 
            HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad,
            Vptr cb (Int.add cofs (Int.repr 216)),
            Vptr pb pofs, Tsh, 64, kv)  opadSHAabs.
    { unfold data_block. rewrite ZLO, HeqOPADcont. 
      (*Issue: same as in ipad loop: need to instantiate Frame manually:
           entailer/entailer!/normalize don't appear to terminate, or creash with "anomaly"*)
      assert (FR : Frame = [FRAME3 kb cb ckb kofs cofs ckoff key ipadSHAabs
                             (default_val t_struct_hmac_ctx_st)]).
        subst Frame; reflexivity.
      rewrite FR; clear FR Frame. 
      simpl. normalize. apply andp_right. apply prop_right. apply isbyte_map_ByteUnsigned. cancel. 
    }
    { rewrite ZLO. intuition. } 

    rename H into opadAbs_def.
    normalize.
    rewrite sublist_same in opadAbs_def; try rewrite ZLO; trivial.

    subst PostResetBranch; entailer.
    unfold FRAME3, sha256state_, default_val; simpl.
    normalize. rename r into iUpd. rename x into oUpd.
    Exists (ipadSHAabs,(iUpd,(opadSHAabs,oUpd))). simpl.
    apply andp_right. apply prop_right. intuition.
    apply andp_right. apply prop_right. intuition.
    cancel.
        unfold data_block. (* initPostResetConditional. simpl.*)
        rewrite ZLO. normalize. cancel.

        (*Issue: VST's canceler fails to cancel the pad terms (Vptr pb pofs), 
            since they';re at different CompSpecs*)
        repeat rewrite <- sepcon_assoc.
        repeat rewrite sepcon_assoc. rewrite sepcon_comm. repeat rewrite <- sepcon_assoc.
        repeat rewrite sepcon_assoc. 
        apply sepcon_derives. eapply derives_trans. apply data_at_data_at_. apply derives_refl.

    unfold data_at at 3. unfold_field_at 2%nat. 
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]).
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]).
    unfold field_address. rewrite if_true; trivial. rewrite if_true; trivial.
  }
  { (*ELSE*) 
    forward. subst. unfold initPostKeyNullConditional. entailer. 
    destruct R; subst. 2: discriminate.
    simpl; clear H. destruct key'; try solve[entailer]. 
    unfold hmacstate_PreInitNull, hmac_relate_PreInitNull; simpl.
    destruct h1; entailer.
    if_tac. Focus 2. entailer. 
    normalize.
    Exists (iSha, (iCtx v, (oSha, oCtx v))). simpl. 
    apply andp_right. apply prop_right. intuition.
    apply andp_right. apply prop_right. intuition.
    cancel.
    unfold hmacstate_PreInitNull, hmac_relate_PreInitNull; simpl.
    Exists v x.
    apply andp_right. apply prop_right. intuition.
    cancel.
   }
intros ? ?. apply andp_left2.  
   unfold POSTCONDITION, abbreviate. rewrite overridePost_overridePost. 
   apply derives_refl. 
Qed.
