Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.
Require Import sha.hmac.
Require Import sha.spec_hmac.
Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.hmac_common_lemmas.

Require Import sha.verif_hmac_init_part1.

(* TODO remove this line and update proof (should become simpler) *)
Ltac canon_load_result Hresult ::= idtac.

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
upd_Znth i
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
  rewrite upd_Znth_app2, Zlength_sublist, Zminus_0_r, Zminus_diag,
     upd_Znth0; repeat rewrite Zlength_sublist; try omega.
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
                   omega.
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
       Vint (Int.repr (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) 0))),upd_Znth i
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
  rewrite upd_Znth_app2, Zlength_sublist, Zminus_0_r, Zminus_diag,
     upd_Znth0; repeat rewrite Zlength_sublist; try omega.
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

Lemma ipad_loop Espec pb pofs cb cofs ckb ckoff kb kofs l key kv (FR:mpred): forall
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
   SEP  (FR;
   data_at Tsh (Tarray tuchar 64 noattr)
       (default_val (Tarray tuchar 64 noattr)) (Vptr pb pofs);
   data_at Tsh (tarray tuchar 64)
       (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff)))
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
      SEP  (FR;
      data_at Tsh (Tarray tuchar 64 noattr) IPADcont (Vptr pb pofs);
      data_at Tsh (tarray tuchar 64)
          (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff)))).
Proof. intros. abbreviate_semax.
eapply semax_post.
Focus 2.
      Time forward_for_simple_bound' 64 (EX i:Z,
        (PROP  ()
         LOCAL  (temp _reset (Vint (Int.repr 1));
           lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
           lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
           temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
           temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
         SEP  (FR;
          data_at Tsh (Tarray tuchar 64 noattr)
             ((sublist 0 i IPADcont) ++ (sublist i 64  (default_val (Tarray tuchar 64 noattr))))
             (Vptr pb pofs);
          data_at Tsh (tarray tuchar 64)
              (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff)))). (*3.6secs*)
      { (*precondition implies "invariant"*)
        rewrite sublist_nil, sublist_same; trivial. simpl app.
        Time entailer!. (*4*)
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

        Time freeze [0;1] FR1. 
        Time forward; rewrite X. (*6.7 versus 9*)
        { entailer!. rewrite <- isbyte_zeroExt8'; trivial.
          apply (isbyteZ_range _ isbyteZQb). }
        Time forward. (*1.9 versus 3.4*)
        unfold Int.xor.
        rewrite Int.unsigned_repr. 2: rewrite int_max_unsigned_eq; omega.
        exploit (isbyteZ_xor 54 qb); trivial. split; omega.
        intros isbyteXOR.
        cbv [cast_int_int].
        rewrite <- (isbyte_zeroExt8 qb); trivial.
        rewrite Int.unsigned_repr. 2: destruct isbyteZQb; rewrite int_max_unsigned_eq; omega.
        rewrite Z.lxor_comm. remember (Vint (Int.repr (Z.lxor qb 54))) as xorval.

        thaw FR1.

        freeze [0; 2] FR2.
        Time forward. (*5.4 versus 5*) (*FIXME NOW takes 20secs; this is the forward the ran out of 2GB memory in the previous version of floyd*)
        Time entailer!. (*5.7 versus 9.6*)
        Time (thaw FR2; simpl; rewrite (*HeqIPADcont,*) UPD_IPAD; simpl; trivial; cancel). (*0.6*)
      }
Unfocus.
cbv beta. rewrite sublist_same, sublist_nil, app_nil_r; trivial.
unfold POSTCONDITION, abbreviate.
intros; apply andp_left2.
apply normal_ret_assert_derives'.
drop_LOCAL 0%nat. apply derives_refl.
subst IPADcont; do 2 rewrite Zlength_map.
unfold HMAC_SHA256.mkArgZ in ZLI; rewrite ZLI; trivial.
Time Qed. (*11.1 versus 16.8*) (*FIXME NOW 39*)

Lemma opadloop Espec pb pofs cb cofs ckb ckoff kb kofs l key kv (FR:mpred): forall
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
   SEP  (FR;
          data_at Tsh (tarray tuchar 64)
              (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff);
   sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108)));
   data_block Tsh
       (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)
       (Vptr pb pofs)))
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
      SEP  (data_at Tsh (tarray tuchar 64)
              (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff);
            sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108)));
            data_at Tsh (Tarray tuchar 64 noattr) OPADcont (Vptr pb pofs);
            FR))).
Proof. intros. abbreviate_semax.
freeze [0;2] FR1.
eapply semax_post.
Focus 2.
      Time forward_for_simple_bound' 64 (EX i:Z,
        (PROP  ()
         LOCAL  (temp _reset (Vint (Int.repr 1));
            lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
            lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
            temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
            temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
         SEP  (FRZL FR1;
              data_at Tsh (tarray tuchar 64)
              (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckoff);
          data_at Tsh (Tarray tuchar 64 noattr)
              ((sublist 0 i OPADcont) ++ (sublist i 64 IPADcont)) (Vptr pb pofs)))).
      { (*precondition implies "invariant"*)
        unfold data_block.
        rewrite sublist_nil, sublist_same; trivial.
          simpl app. Time entailer!. (*6 versus 3.1 -- penalty?*)
          rewrite ZLI. unfold tarray, HMAC_SHA256.mkArgZ. trivial.
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
        freeze [0;2] FR2.
        Time forward; rewrite X. (*5.3 versus 7.8, and we've eliminated some floyds preceding the call*)
        { Time entailer!. (*1.8 versus 2.9*)
          rewrite <- isbyte_zeroExt8'; trivial; apply (isbyteZ_range _ isbyteZQb).
        }
        thaw FR2.
       (*doing freeze [0; 2] FR3. here lets the entailer! 2 lines below take 11 secs instead of 5,
           with a residual subgoal thats more complex to discharge*)
        Time forward. (*5.8 versus 4.8*) (*FIXME NOW: 19 secs*)
        Time entailer!. (*4.2 versus 5.6*)
        rewrite field_at_data_at.
        rewrite field_address_offset by auto with field_compatible.
        simpl; rewrite Int.add_zero.
        apply derives_refl'. f_equal. apply UPD_OPAD; eassumption.
      }
Unfocus.
cbv beta. rewrite sublist_same, sublist_nil, app_nil_r; trivial.
thaw' FR1.
Time entailer!. (*3.4 versus 2.6*)
subst OPADcont; do 2 rewrite Zlength_map.
unfold HMAC_SHA256.mkArgZ in ZLO; rewrite ZLO; trivial.
Time Qed. (*12.3 versus 18.7*)  (*FIXME NOW 36secs*)

Lemma init_part2: forall MYPOST
(Espec : OracleKind)
(c : val)
(k : val)
(l : Z)
(key : list Z)
(kv : val)
(h1 : hmacabs)
(*(Delta := initialized _reset
       (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs))*)
(cb : block)
(cofs : int)
(pad : val)
(r : Z)
(ckb : block)
(ckoff : int)
(R : r = 0 \/ r = 1)
(PostResetBranch : environ -> mpred)
(HeqPostResetBranch : PostResetBranch = EX shaStates:_ ,
          PROP  (innerShaInit (map Byte.repr (HMAC_SHA256.mkKey key))
                         =  (fst shaStates) /\
                  s256_relate (fst shaStates) (fst (snd shaStates)) /\
                  outerShaInit (map Byte.repr (HMAC_SHA256.mkKey key))
                          = (fst (snd (snd shaStates))) /\
                  s256_relate (fst (snd (snd shaStates))) (snd (snd (snd shaStates))))
          LOCAL  (lvar _pad (tarray tuchar 64) pad;
                  lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
                  temp _ctx (Vptr cb cofs); temp _key k;
                  temp _len (Vint (Int.repr l));
                  gvar sha._K256 kv)
          SEP  (data_at_ Tsh (tarray tuchar 64) pad;
                data_at_ Tsh (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
                initPostResetConditional r (Vptr cb cofs) k h1 key (fst (snd shaStates)) (snd (snd (snd shaStates)));
                K_vector kv)),
@semax CompSpecs Espec (*Delta*) (initialized _reset
       (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs))
  (PROP  ()
   LOCAL  (temp _reset (Vint (Int.repr r));
   lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff); lvar _pad (tarray tuchar 64) pad;
   temp _ctx (Vptr cb cofs); temp _key k; temp _len (Vint (Int.repr l));
   gvar sha._K256 kv)
   SEP  (data_at_ Tsh (tarray tuchar 64) pad;
         initPostKeyNullConditional r (Vptr cb cofs) k h1 key (Vptr ckb ckoff);
         K_vector kv))
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
    (overridePost PostResetBranch MYPOST)(*     (frame_ret_assert
         (function_body_ret_assert tvoid
            (EX  h : hmacabs,
             PROP  (hmacInit key h)
             LOCAL ()
             SEP  (hmacstate_ h (Vptr cb cofs); initPostKey k key;
             K_vector kv)))
         (`(EX  v : val,
           local (lvar _pad (tarray tuchar 64) v) &&
           data_at_ Tsh (tarray tuchar 64) v)) *
          `(EX  v : val,
           local (lvar _ctx_key (tarray tuchar 64) v) &&
           data_at_ Tsh (tarray tuchar 64) v)))*).
Proof. intros. abbreviate_semax.
forward_if PostResetBranch.
  { (* THEN*)
    rename H into r_true.
    destruct R as [R | R]; [subst r; contradiction r_true; reflexivity | ].
    subst r; clear r_true.
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
    Time assert_PROP (isptr pad) as Ppad by entailer!. (*1*)
    apply isptrD in Ppad; destruct Ppad as [pb [pofs Hpad]]. subst pad.

    apply semax_pre with (P':=EX b:_, EX i:_,
       PROP  (k=Vptr b i /\ Forall isbyteZ key)
       LOCAL  (temp _reset (Vint (Int.repr 1));
              lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
              lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
              temp _ctx (Vptr cb cofs); temp _key (Vptr b i);
              temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
       SEP  (@data_at CompSpecs Tsh t_struct_hmac_ctx_st HMS (Vptr cb cofs);
             @data_at CompSpecs Tsh (tarray tuchar 64)
                  (@map int val Vint (@map Z int Int.repr (HMAC_SHA256.mkKey key)))
                  (Vptr ckb ckoff);
            @data_at CompSpecs Tsh (tarray tuchar (@Zlength Z key))
                  (@map int val Vint (@map Z int Int.repr key)) (Vptr b i);
            @field_at_ CompSpecs Tsh (Tarray tuchar 64 noattr) [] (Vptr pb pofs);
            K_vector kv)).
    { clear POSTCONDITION HeqPostResetBranch PostResetBranch.
      unfold initPostKeyNullConditional.
      go_lower. ent_iter. (* Issue: we just want these two parts of entailer here... *)
      destruct k; try contradiction.
      Time if_tac; entailer!. (* 0.92 *)
      Exists b i.
      (*04/21/17: entailer! used to solve this in 6.7secs but now takes > 30secs;
       the following is a little faster.*)
      normalize. apply andp_right. apply prop_right; repeat split; trivial.
          Time entailer; cancel. }
    Intros kb kofs.
    rename H into isbyte_key.

(*to be proven in veric: a frame rule for frozen assertions:
Lemma semax_freeze n Espec {cs: compspecs} Delta P Q  R Rs c xs ys P' Q' R':
 R = map liftx Rs ->
 nth n Rs emp = FRZL xs ->
 delete_nth n Rs = ys ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (map liftx ys)))) c (normal_ret_assert (PROPx P' (LOCALx Q' (SEPx R')))) ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c (normal_ret_assert (PROPx P' (LOCALx Q' (SEPx (map liftx xs ++ R'))))).
Proof. intros. subst.
rewrite semax_unfold.
eapply semax_pre_post. 3: eassumption. 2: intros; entailer.
apply andp_left2. unfold PROPx. normalize.
unfold LOCALx. apply derives_refl'.
f_equal. unfold SEPx. clear - H0.
rewrite map_app, fold_right_sepcon_app. rewrite FRZL_ax in H0.
rewrite (fold_right_sepcon_deletenth' n). rewrite map_delete_nth. f_equal.
rewrite mapnth' with (d:=emp); try reflexivity.
extensionality. rewrite fold_right_sepcon_liftx, <- H0. trivial.
Qed.*)

       assert (ZZ: exists HMS':reptype t_struct_hmac_ctx_st, HMS'=HMS). exists HMS. trivial.
       destruct ZZ as [HMS' HH].
       remember (K_vector kv * data_at Tsh t_struct_hmac_ctx_st HMS' (Vptr cb cofs)
                          * data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
                         (Vptr kb kofs)) as myPred.
    forward_seq.
    { (*ipad loop*)
      (*semax_subcommand HmacVarSpecs HmacFunSpecs f_HMAC_Init.*)
       eapply semax_pre.
       Focus 2. eapply (ipad_loop Espec pb pofs cb cofs ckb ckoff kb kofs l key kv myPred); try eassumption.
       subst HMS'. clear - HeqmyPred. Time entailer!; cancel. (*
      eapply semax_pre. Focus 2. eapply (ipad_loop Espec pb pofs cb cofs ckb ckoff kb kofs l key kv
                      (K_vector kv * data_at Tsh t_struct_hmac_ctx_st HMS' (Vptr cb cofs)
                          * data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
                         (Vptr kb kofs))).
                eassumption. eassumption. eassumption.
       clear HeqPostResetBranch. go_lower. apply andp_right. apply prop_right; trivial.
            apply andp_right. apply prop_right; intuition.
       assert (HFR: ?FR = (K_vector kv * data_at Tsh t_struct_hmac_ctx_st HMS(*'*) (Vptr cb cofs)
                          * data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
                         (Vptr kb kofs))). cancel.  apply andp_left2.
         entailer!. cancel. ; try eassumption.
      eapply semax_pre_post.
      Focus 3. remember (data_at Tsh t_struct_hmac_ctx_st HMS(*'*) (Vptr cb cofs)) as myFR1. K_vector kv * data_at Tsh t_struct_hmac_ctx_st HMS(*'*) (Vptr cb cofs)
                          * data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
                         (Vptr kb kofs)) as myFR. (data_at Tsh t_struct_hmac_ctx_st HMS (Vptr cb cofs)).
 specialize (ipad_loop Espec pb pofs cb cofs ckb ckoff kb kofs l key kv). eapply  (*HMS' *)
                         (K_vector kv * data_at Tsh t_struct_hmac_ctx_st HMS(*'*) (Vptr cb cofs)
                          * data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
                         (Vptr kb kofs))). try eassumption.
      Time entailer!. (*8.7 *) apply derives_refl.
      intros ? ?. apply andp_left2. apply derives_refl.*)
    }
    subst myPred HMS'.

    (*continuation after ipad-loop*)
    Time normalize. (*3.4*)
    freeze [2;3;4] FR1.
    Time (assert_PROP (field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs)) as FC_C
       by entailer!). (*1.9 versus 6.5*)
    Time unfold_data_at 1%nat. (*1*)
    freeze [0;1;4] FR2.
    rewrite (field_at_data_at  Tsh t_struct_hmac_ctx_st [StructField _i_ctx]).
    assert_PROP (field_compatible t_struct_hmac_ctx_st [StructField _i_ctx] (Vptr cb cofs)) as FC_ICTX.
    { apply prop_right. clear - FC_C. red in FC_C.
      repeat split; try solve [apply FC_C]. right; left; trivial. }
    rewrite field_address_offset by auto with field_compatible.
    simpl.

    (*Call to _SHA256_Init*)
    Time forward_call (Vptr cb (Int.add cofs (Int.repr 108))). (*9.5 versus 10.5*)

    (*Call to _SHA256_Update*)
    thaw FR2.
    thaw FR1.
    freeze [1;3;5;6] FR3.
    Time forward_call (@nil Z,
                  HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad,
                  Vptr cb (Int.add cofs (Int.repr 108)), Vptr pb pofs, Tsh, 64, kv).
        (*4 versus 10.5*)
    { assert (FR : Frame = [FRZL FR3]).
        subst Frame; reflexivity.
      rewrite FR; clear FR Frame.
      simpl. Time cancel. (*0.3*)
      unfold data_block. rewrite  ZLI, HeqIPADcont. unfold HMAC_SHA256.mkArgZ.
      simpl. Time entailer!. (*0.9*) apply isbyte_map_ByteUnsigned.
    }
    { clear HeqPostResetBranch HeqOPADcont(*; subst IPADcont*).
        rewrite Zlength_mkArgZ. repeat rewrite map_length. rewrite mkKey_length. intuition.
    }
    simpl.
    rewrite sublist_same; try rewrite ZLI; trivial.
    remember (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad) as ipadSHAabs.

    (*essentially the same for opad*)
    thaw FR3.
    freeze [0; 3; 5;6] FR4.
    forward_seq.
    { (*opad loop*)
      eapply semax_pre.
      2: apply (opadloop Espec pb pofs cb cofs ckb ckoff kb kofs l key kv (FRZL FR4) IPADcont) with (ipadSHAabs:=ipadSHAabs); try reflexivity; subst ipadSHAabs; try assumption.
      entailer!.
    }

    (*continuation after opad-loop*)
    thaw FR4.
    freeze [0;1;4;6] FR5.
    freeze [0;1;2] FR6.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]).
    assert_PROP (field_compatible t_struct_hmac_ctx_st [StructField _o_ctx] (Vptr cb cofs)) as FC_OCTX.
    { apply prop_right. clear - FC_C. red in FC_C. 
      repeat split; try solve [apply FC_C]. right; right; left; trivial. }
    rewrite field_address_offset by auto with field_compatible.

    (*Call to _SHA256_Init*)
    unfold MORE_COMMANDS, abbreviate.

    Time forward_call (Vptr cb (Int.add cofs (Int.repr 216))). (*6.4 versus 10.6*)

    (* Call to sha_update*)
    thaw FR6.
    Time forward_call (@nil Z,
            HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad,
            Vptr cb (Int.add cofs (Int.repr 216)),
            Vptr pb pofs, Tsh, 64, kv). (*4.5*)
    { assert (FR : Frame = [FRZL FR5]).
        subst Frame; reflexivity.
      rewrite FR; clear FR Frame.
      unfold data_block. simpl.
      rewrite ZLO; trivial.
      Time entailer!. (*1.5*) apply isbyte_map_ByteUnsigned. (*superfluous.. apply derives_refl.*)
    }
    { rewrite ZLO; intuition. }

    rewrite sublist_same; try rewrite ZLO; trivial.

    Time subst PostResetBranch; entailer!. (*4.7 *)
    thaw FR5. unfold sha256state_, data_block.
    rewrite ZLO. (*superfluous...subst ipadSHAabs.*)
    Intros oUpd iUpd.
    change_compspecs CompSpecs.
    Exists (innerShaInit (map Byte.repr (HMAC_SHA256.mkKey key)),(iUpd,(outerShaInit (map Byte.repr (HMAC_SHA256.mkKey key)),oUpd))).
    simpl. rewrite !prop_true_andp by (auto; intuition).
    Time cancel. (*5 versus 4*)
    unfold_data_at 3%nat.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]).
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]).
    rewrite field_address_offset by auto with field_compatible.
    rewrite field_address_offset by auto with field_compatible.
    Time cancel. (*0.5*)
  }
  { (*ELSE*)
    Time forward. (*0.2*)
    subst. unfold initPostKeyNullConditional. Time entailer!.  (*6.5*)
    destruct R; subst; [ |discriminate].
    simpl; clear H. Time destruct k; try solve[entailer]. (*2.9*)
    unfold hmacstate_PreInitNull, hmac_relate_PreInitNull; simpl.
    Time if_tac; [ | entailer!].
    Intros v x. destruct h1.
    Exists (iSha, (iCtx v, (oSha, oCtx v))). simpl.
    unfold hmacstate_PreInitNull, hmac_relate_PreInitNull; simpl.
    Exists v x.
    change (Tarray tuchar 64 noattr) with (tarray tuchar 64).
    rewrite !prop_true_andp by (auto; intuition). 
    (* 04/21/17: Script used to say cancel (*0.7secs*).
       But cancel now takes 43 secs.
       solve [entailer; cancel] takes 16.9secs
       solve [entailer!; cancel] takes 43secs*) 
     Time solve [entailer; cancel]. (*16.9secs*)
   } 
intros ? ?. apply andp_left2.
   unfold POSTCONDITION, abbreviate. rewrite overridePost_overridePost.
   apply derives_refl.
Time Qed. (*60 versus 63*) (*FIXME NOW: 80secs*) (*Coq8.5pl1: 20secs*)
