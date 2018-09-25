Require Import VST.floyd.proofauto.
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

(*TODO: eliminate*)
Ltac canon_load_result ::= idtac.

Lemma isbyte_zeroExt8: forall x,
    0 <= x <= Byte.max_unsigned -> 
   Int.repr x = (Int.zero_ext 8 (Int.repr x)).
Proof. intros. rewrite zero_ext_inrange. trivial.
  simpl.  rewrite Int.unsigned_repr. rep_omega. rep_omega.
Qed.

Lemma isbyte_zeroExt8' : forall x, Int.unsigned (Int.zero_ext 8 x) <= Byte.max_unsigned.
Proof.
intros.
pose proof (Int.zero_ext_range 8 x).
spec H. computable. change (two_p 8) with 256 in H. rep_omega.
Qed.

(*
Lemma eval_cast_tuchar_of_isbyteZ q: isbyteZ q ->
      eval_cast tuchar tuchar (Vint (Int.repr q)) = Vint (Int.repr q).
Proof. unfold eval_cast. simpl. intros. f_equal. apply zero_ext_inrange. simpl.
  destruct H.
  rewrite Int.unsigned_repr. omega. rewrite int_max_unsigned_eq. omega.
Qed.

Lemma Znth_map_Vint_is_int_I8: forall l (i : Z) (F: Forall isbyteZ l),
       0 <= i < Zlength l ->
is_int I8 Unsigned
  (Znth i (map Vint (map Int.repr l))).
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
  (Znth i (map Vint (map Int.repr (map Byte.unsigned l)))).
Proof. intros. apply Znth_map_Vint_is_int_I8.
  apply isbyte_map_ByteUnsigned.
  rewrite Zlength_map; trivial.
Qed.
*)

Lemma UPD_IPAD: forall
  (key : list byte)
  (ZLI : Zlength
        (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Ipad) =
      64)
  (i : Z)
  (I : 0 <= i < 64)
  (X : Znth i (map Vubyte (HMAC_SHA256.mkKey key)) =
      Vubyte (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) Byte.zero)),
upd_Znth i
  (sublist 0 i
     (map Vubyte
              (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Ipad)) ++
   sublist i 64 (default_val (Tarray tuchar 64 noattr)))
  (Vubyte
        (Byte.xor (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) Byte.zero) (Byte.repr 54))) =
sublist 0 (i + 1)
  (map Vubyte
           (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Ipad)) ++
sublist (i + 1) 64 (default_val (Tarray tuchar 64 noattr)).
Proof. intros. 
  rewrite upd_Znth_app2, Zlength_sublist, Zminus_0_r, Zminus_diag,
     upd_Znth0; repeat rewrite Zlength_sublist; try omega.
  2: rewrite Zlength_default_val_Tarray_tuchar; omega.
  2: rewrite Zlength_map; rewrite ZLI; omega.
  2: rewrite Zlength_default_val_Tarray_tuchar; omega.
  2: rewrite Zlength_map; rewrite ZLI; omega.
  rewrite <- (sublist_rejoin 0 i (i+1)); try omega.
  2: rewrite Zlength_map; rewrite ZLI; omega.
  rewrite <- app_assoc. f_equal.
  rewrite (sublist_len_1 i); simpl app.
  2: rewrite Zlength_map; rewrite ZLI; omega.
  f_equal. rewrite Znth_map. f_equal.
           unfold HMAC_SHA256.mkArg.
           unfold Znth. unfold Znth in X. destruct (zlt i 0). discriminate.
           specialize (map_nth (fun p : byte * byte => Byte.xor (fst p) (snd p))
                                       (combine (HMAC_SHA256.mkKey key) (HMAC_SHA256.sixtyfour Ipad))
                                       (Byte.zero, Byte.zero)
                                       (Z.to_nat i)). simpl.
           rewrite Byte.xor_zero; intros MN.
           change Inhabitant_byte with Byte.zero.
           rewrite MN; clear MN.
                   rewrite combine_nth.
                   2:{ rewrite length_SF, mkKey_length. reflexivity. }
                   unfold fst, snd. 
                   remember (HMAC_SHA256.sixtyfour Ipad).
                   assert (NTH: nth (Z.to_nat i) l Byte.zero = Byte.repr 54).
                     subst l. apply nth_list_repeat'. apply (Z2Nat.inj_lt _ 64). apply I. omega. omega.
                   rewrite NTH. auto. 
                   rewrite ZLI; assumption.
  rewrite sublist_sublist; try omega.
  assert (64 - i + i = 64) by omega. rewrite Zplus_comm, H; trivial.
Qed.

Lemma UPD_OPAD: forall
  (key : list byte)
  (ZLI : Zlength (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Ipad) = 64)
  (ZLO : Zlength (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Opad) = 64)
  (i : Z)
  (I : 0 <= i < 64)
  (X : Znth i (map Vubyte (HMAC_SHA256.mkKey key)) =
       Vubyte (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) Byte.zero)),upd_Znth i
  (sublist 0 i
     (map Vubyte
              (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Opad)) ++
   sublist i 64
     (map Vubyte
              (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Ipad)))
  (Vubyte
        (Byte.xor (Byte.repr 92)
              (nth (Z.to_nat i) (HMAC_SHA256.mkKey key) Byte.zero))) =
sublist 0 (i + 1)
  (map Vubyte (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Opad)) ++
sublist (i + 1) 64
  (map Vubyte (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Ipad)).
Proof. intros. 
  rewrite upd_Znth_app2, Zlength_sublist, Zminus_0_r, Zminus_diag,
     upd_Znth0; repeat rewrite Zlength_sublist; try omega.
  2: rewrite Zlength_map, ZLI; omega.
  2: rewrite Zlength_map, ZLO; omega.
  2: rewrite Zlength_map, ZLI; omega.
  2: rewrite Zlength_map, ZLO; omega.
  rewrite <- (sublist_rejoin 0 i (i+1)); try omega.
  2: rewrite Zlength_map, ZLO; omega.
  rewrite <- app_assoc. f_equal.
  rewrite (sublist_len_1 i); simpl app.
  2: rewrite Zlength_map, ZLO; omega.
  f_equal. rewrite Znth_map. f_equal.
           unfold HMAC_SHA256.mkArg.
           unfold Znth. unfold Znth in X. destruct (zlt i 0). discriminate.
           specialize (map_nth (fun p : byte * byte => Byte.xor (fst p) (snd p))
                                       (combine (HMAC_SHA256.mkKey key) (HMAC_SHA256.sixtyfour Opad))
                                       (Byte.zero, Byte.zero)
                                       (Z.to_nat i)). simpl.
           rewrite Byte.xor_zero; intros MN.
           change Inhabitant_byte with Byte.zero.
           rewrite MN; clear MN.
                   rewrite combine_nth.
                   2:{ rewrite length_SF, mkKey_length. reflexivity. }
                   rewrite Byte.xor_commut.
                    unfold fst, snd.
                   remember (HMAC_SHA256.sixtyfour Opad).
                   assert (NTH: nth (Z.to_nat i) l Byte.zero = Byte.repr 92).
                     subst l. apply nth_list_repeat'. apply (Z2Nat.inj_lt _ 64). apply I. omega. omega.
                   rewrite NTH; trivial.
                   rewrite ZLO; assumption.
  rewrite sublist_sublist; try omega.
  assert (64 - i + i = 64) by omega. rewrite Zplus_comm, H; trivial.
Qed.

(*Definition postResetHMS (iS oS: s256state): hmacstate :=
  (emptySha, (iS, oS)).*)
Definition postResetHMS (iS oS: s256state): hmacstate :=
  (default_val t_struct_SHA256state_st, (iS, oS)).

Definition initPostResetConditional r (c:val) (k: val) h wsh sh key iS oS: mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0 then hmacstate_PreInitNull wsh key h c else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF
                  else ((data_at wsh t_struct_hmac_ctx_st (postResetHMS iS oS) c) *
                        (data_at sh (tarray tuchar (Zlength key)) (map Vubyte key) (Vptr b ofs)))
  | _ => FF
  end.

Lemma ipad_loop Espec pb pofs cb cofs ckb ckoff kb kofs l key gv (FR:mpred): forall
(IPADcont : list val)
(HeqIPADcont : IPADcont =
              map Vubyte
                      (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Ipad))
(ZLI : Zlength
        (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Ipad) =
      64),
@semax CompSpecs Espec
  (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs nil)
  (PROP  ()
   LOCAL  (temp _reset (Vint (Int.repr 1));
   lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
   lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
   temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
   temp _len (Vint (Int.repr l)); gvars gv)
   SEP  (FR;
   data_at Tsh (Tarray tuchar 64 noattr)
       (default_val (Tarray tuchar 64 noattr)) (Vptr pb pofs);
   data_at Tsh (tarray tuchar 64)
       (map Vubyte (HMAC_SHA256.mkKey key)) (Vptr ckb ckoff)))
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
      temp _len (Vint (Int.repr l)); gvars gv)
      SEP  (FR;
      data_at Tsh (Tarray tuchar 64 noattr) IPADcont (Vptr pb pofs);
      data_at Tsh (tarray tuchar 64)
          (map Vubyte (HMAC_SHA256.mkKey key)) (Vptr ckb ckoff)))).
Proof. intros. abbreviate_semax.
       forward_for_simple_bound 64 (EX i:Z,
        (PROP  ()
         LOCAL  (temp _reset (Vint (Int.repr 1));
           lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
           lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
           temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
           temp _len (Vint (Int.repr l)); gvars gv)
         SEP  (FR;
          data_at Tsh (Tarray tuchar 64 noattr)
             ((sublist 0 i IPADcont) ++ (sublist i 64  (default_val (Tarray tuchar 64 noattr))))
             (Vptr pb pofs);
          data_at Tsh (tarray tuchar 64)
              (map Vubyte (HMAC_SHA256.mkKey key)) (Vptr ckb ckoff)))). (*3.6secs*)
      { (*precondition implies "invariant"*)
        rewrite sublist_nil, sublist_same; auto.
        apply ENTAIL_refl.
      }
      { rename H into I.
        assert (Xb: exists qb, nth (Z.to_nat i) (HMAC_SHA256.mkKey key) Byte.zero = qb).
          { destruct (nth_mapIn (Z.to_nat i) (HMAC_SHA256.mkKey key) Byte.zero) as [? [? ?]].
             rewrite mkKey_length.
              split. apply (Z2Nat.inj_le 0); omega. apply (Z2Nat.inj_lt _ 64); omega.
            exists x; trivial.
          }
        destruct Xb as [qb Qb].
        assert (X: Znth i (map Vubyte (HMAC_SHA256.mkKey key))
                   = Vubyte qb). (* (Int.zero_ext 8 q)).*)
          { unfold Znth. destruct (zlt i 0). omega.
            rewrite nth_indep with (d':=Vubyte Byte.zero).
            2:{ repeat rewrite map_length. rewrite mkKey_length. unfold SHA256.BlockSize; simpl. apply (Z2Nat.inj_lt _ 64); omega. }
            repeat rewrite map_nth. rewrite Qb. trivial.
          }

        Time freeze [0;1] FR1.
        Time forward; (*6.7 versus 9*)
        change Inhabitant_val with Vundef in X;
         rewrite X.
        { entailer!. apply isbyte_zeroExt8'. }
        Time forward. (*1.9 versus 3.4*)
        unfold Int.xor.
        rewrite Int.unsigned_repr. 2: rewrite int_max_unsigned_eq; omega.
        cbv [cast_int_int].
        rewrite <- (isbyte_zeroExt8 (Byte.unsigned qb)) by rep_omega.
        rewrite Int.unsigned_repr by rep_omega.
        assert (H54: 0 <= Z.lxor 54 (Byte.unsigned qb) <= Byte.max_unsigned). {rewrite (xor_inrange 54 (Byte.unsigned qb)).
           pose proof (Z.mod_pos_bound (Z.lxor 54 (Byte.unsigned qb)) Byte.modulus).
           spec H; [rep_omega|]. rep_omega. reflexivity.
           symmetry; apply Z.mod_small. pose proof (Byte.unsigned_range qb); rep_omega.
        }
        rewrite <- isbyte_zeroExt8 by auto.
        replace (Vint (Int.repr (Z.lxor 54 (Byte.unsigned qb))))
        with (Vubyte (Byte.xor (Byte.repr 54) qb)).
       2:{   unfold Vubyte. f_equal. f_equal. unfold Byte.xor.
              rewrite (Byte.unsigned_repr  54) by rep_omega.
              apply Byte.unsigned_repr; auto.
          }
        rewrite Byte.xor_commut. remember (Vubyte (Byte.xor qb (Byte.repr 54))) as xorval.

        thaw FR1.

        freeze [0; 2] FR2.
        Time forward. (*5.4 versus 5*) (*FIXME NOW takes 20secs; this is the forward the ran out of 2GB memory in the previous version of floyd*)
        Time entailer!. (*5.7 versus 9.6*)
         thaw FR2; simpl.
        rewrite <- isbyte_zeroExt8 by rep_omega.
        change (Vint (Int.repr (Byte.unsigned ?A))) with (Vubyte A).
        Time (rewrite (*HeqIPADcont,*) UPD_IPAD; simpl; trivial; cancel). (*0.6*)
      }
cbv beta. rewrite sublist_same, sublist_nil, app_nil_r; trivial.
intros; apply andp_left2.
drop_LOCAL 0%nat. apply derives_refl.
subst IPADcont; rewrite Zlength_map. rewrite ZLI; trivial.
Time Qed. (*VST 2.0: 0.4s*) (*11.1 versus 16.8*) (*FIXME NOW 39*)

Lemma opadloop Espec pb pofs cb cofs ckb ckoff kb kofs l wsh key gv (FR:mpred): forall
(Hwsh: writable_share wsh)
(IPADcont : list val)
(HeqIPADcont : IPADcont =
              map Vubyte
                      (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Ipad))
(OPADcont : list val)
(HeqOPADcont : OPADcont =
              map Vubyte
                      (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Opad))
(ZLI : Zlength (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Ipad) = 64)
(ZLO : Zlength (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Opad) = 64)
(*Delta := abbreviate : tycontext*)
(ipadSHAabs : s256abs),
@semax CompSpecs Espec
  (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs nil)
  (PROP  ()
   LOCAL  (temp _reset (Vint (Int.repr 1));
   lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
   lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
   temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
   temp _len (Vint (Int.repr l)); gvars gv)
   SEP  (FR;
          data_at Tsh (tarray tuchar 64)
              (map Vubyte(HMAC_SHA256.mkKey key)) (Vptr ckb ckoff);
   sha256state_ wsh ipadSHAabs (Vptr cb (Ptrofs.add cofs (Ptrofs.repr 108)));
   data_block Tsh (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Ipad)
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
             temp _key (Vptr kb kofs); temp _len (Vint (Int.repr l)); gvars gv)
      SEP  (data_at Tsh (tarray tuchar 64)
              (map Vubyte (HMAC_SHA256.mkKey key)) (Vptr ckb ckoff);
            sha256state_ wsh ipadSHAabs (Vptr cb (Ptrofs.add cofs (Ptrofs.repr 108)));
            data_at Tsh (Tarray tuchar 64 noattr) OPADcont (Vptr pb pofs);
            FR))).
Proof. intros. abbreviate_semax.
freeze [0;2] FR1.
      forward_for_simple_bound 64 (EX i:Z,
        (PROP  ()
         LOCAL  (temp _reset (Vint (Int.repr 1));
            lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
            lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
            temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
            temp _len (Vint (Int.repr l)); gvars gv)
         SEP  (FRZL FR1;
              data_at Tsh (tarray tuchar 64)
              (map Vubyte (HMAC_SHA256.mkKey key)) (Vptr ckb ckoff);
          data_at Tsh (Tarray tuchar 64 noattr)
              ((sublist 0 i OPADcont) ++ (sublist i 64 IPADcont)) (Vptr pb pofs)))).
      { (*precondition implies "invariant"*)
        unfold data_block.
        rewrite sublist_nil, sublist_same; trivial.
          simpl app. Time entailer!. (*6 versus 3.1 -- penalty?*)
          rewrite ZLI. unfold tarray. apply derives_refl.
          subst IPADcont. rewrite Zlength_map. rewrite ZLI. trivial.
      }
      { rename H into I.
        assert (Xb: exists qb, nth (Z.to_nat i) (HMAC_SHA256.mkKey key) Byte.zero = qb).
          { destruct (nth_mapIn (Z.to_nat i) (HMAC_SHA256.mkKey key) Byte.zero) as [? ?].
             rewrite mkKey_length.
              split. apply (Z2Nat.inj_le 0); omega. apply (Z2Nat.inj_lt _ 64); omega.
            exists x; trivial. destruct H; auto.
          }
        destruct Xb as [qb Qb].
        assert (X: Znth i (map Vubyte (HMAC_SHA256.mkKey key))
                   = Vubyte qb). (* (Int.zero_ext 8 q)).*)
          { unfold Znth. destruct (zlt i 0). omega.
            rewrite nth_indep with (d':=Vubyte Byte.zero).
              2:{ repeat rewrite map_length. rewrite mkKey_length. unfold SHA256.BlockSize; simpl. apply (Z2Nat.inj_lt _ 64); omega. }
            repeat rewrite map_nth. rewrite Qb. trivial.
          }
        freeze [0;2] FR2.
        Time forward;
        change Inhabitant_val with Vundef in X;
        rewrite X.  (*5.3 versus 7.8, and we've eliminated some floyds preceding the call*)
        { Time entailer!. (*1.8 versus 2.9*)
          apply isbyte_zeroExt8'.
        }
        thaw FR2.
       (*doing freeze [0; 2] FR3. here lets the entailer! 2 lines below take 11 secs instead of 5,
           with a residual subgoal thats more complex to discharge*)
        Time forward. (*5.8 versus 4.8*) (*FIXME NOW: 19 secs*)
        Time entailer!. (*4.2 versus 5.6*)
        apply derives_refl'. f_equal.
        set (y := nth (Z.to_nat i) (HMAC_SHA256.mkKey key) Byte.zero).
        rewrite <- (isbyte_zeroExt8 (Byte.unsigned _)) by rep_omega.
        unfold Int.xor. rewrite !Int.unsigned_repr by rep_omega.
        rewrite xor_inrange. 2: reflexivity.
        2:{  clear; symmetry; apply Z.mod_small.
               pose proof (Byte.unsigned_range y); rep_omega.
         }
        rewrite <- isbyte_zeroExt8.
       2:{ clear. pose proof (Z_mod_lt (Z.lxor 92 (Byte.unsigned y)) Byte.modulus).
            spec H; [rep_omega|]. rep_omega.
         }
        replace (Vint (Int.repr (Z.lxor 92 (Byte.unsigned y) mod Byte.modulus)))
          with (Vubyte (Byte.xor (Byte.repr 92) y)).
         2:{ unfold Vubyte. f_equal. f_equal.
               unfold Byte.xor. rewrite (Byte.unsigned_repr 92) by rep_omega.
               apply Byte.unsigned_repr_eq.
           }
        apply UPD_OPAD; try eassumption.
        rewrite <- X. autorewrite with sublist. auto.
      }
cbv beta. rewrite sublist_same, sublist_nil, app_nil_r; trivial.
thaw' FR1.
Time entailer!. (*3.4 versus 2.6*)
subst OPADcont; rewrite Zlength_map.
rewrite ZLO; trivial.
Time Qed. (*VST 2.0: 0.4s*) (*12.3 versus 18.7*)  (*FIXME NOW 36secs*)
