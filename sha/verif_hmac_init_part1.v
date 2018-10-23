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
Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.hmac_common_lemmas.
Require Import sha.spec_hmac.

Lemma change_compspecs_t_struct_SHA256state_st':
  @data_at_ spec_sha.CompSpecs Ews t_struct_SHA256state_st =
  @data_at_ CompSpecs Ews t_struct_SHA256state_st.
Proof.
  extensionality v.
  change (@data_at_ spec_sha.CompSpecs Ews t_struct_SHA256state_st v) with
      (@data_at spec_sha.CompSpecs Ews t_struct_SHA256state_st (default_val _) v).
  change (@data_at_ CompSpecs Ews t_struct_SHA256state_st v) with
      (@data_at CompSpecs Ews t_struct_SHA256state_st (default_val _) v).
  rewrite change_compspecs_t_struct_SHA256state_st.
  auto.
Qed.

Hint Rewrite change_compspecs_t_struct_SHA256state_st' : norm.

Definition initPostKeyNullConditional r (c:val) (k: val) h wsh sh key ctxkey: mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0
                   then (hmacstate_PreInitNull wsh key h c) * (data_at_ Tsh (tarray tuchar 64) ctxkey)
                   else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF
                  else 
                    ((data_at wsh t_struct_hmac_ctx_st (*keyed*)HMS c) *
                     (data_at Tsh (tarray tuchar 64) (map Vubyte (HMAC_SHA256.mkKey key))
                      ctxkey)  *
                     (data_at sh (tarray tuchar (Zlength key)) (map Vubyte key)
                      (Vptr b ofs)))
  | _ => FF
  end.

Definition PostKeyNull c k pad gv h1 l wsh sh key ckb ckoff: environ -> mpred :=
                 EX  cb : block,
                 (EX  cofs : ptrofs,
                  (EX  r : Z,
                   PROP  (c = Vptr cb cofs /\ (r = 0 \/ r = 1))
                   LOCAL  (temp _reset (Vint (Int.repr r));
                   lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
                   lvar _pad (tarray tuchar 64) pad; temp _ctx c;
                   temp _key k; temp _len (Vint (Int.repr l));
                   gvars gv)
                   SEP  (data_at_ Tsh (tarray tuchar 64) pad;
                   initPostKeyNullConditional r c k h1 wsh sh key (Vptr ckb ckoff);
                   K_vector gv))).

Lemma Init_part1_j_lt_len Espec (kb ckb cb: block) (kofs ckoff cofs: ptrofs)
           l wsh sh (key: list byte) gv pad
      (HMS' : reptype t_struct_hmac_ctx_st): forall 
(Hwsh: writable_share wsh)
(Hsh: readable_share sh)
(KL1 : l = Zlength key)
(KL2 : 0 < l <= Int.max_signed)
(KL3 : l * 8 < two_p 64)
(HMS' : reptype t_struct_hmac_ctx_st)
(KHMS : HMS' = HMS)
(FC_ctx : field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs))
(FC_md_ctx : field_compatible t_struct_hmac_ctx_st [StructField _md_ctx]
              (Vptr cb cofs))
(FC_cxtkey : field_compatible (Tarray tuchar 64 noattr) [] (Vptr ckb ckoff))
(lt_64_l : 64 < l),
@semax CompSpecs Espec
       (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs nil)
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr 64)); temp _reset (Vint (Int.repr 1));
   lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
   lvar _pad (tarray tuchar 64) pad; temp _ctx (Vptr cb cofs);
   temp _key (Vptr kb kofs); temp _len (Vint (Int.repr l));
   gvars gv)
   SEP  (data_at sh (tarray tuchar (Zlength key)) (map Vubyte key)
        (Vptr kb kofs); data_at_ Tsh (tarray tuchar 64) pad;
   K_vector gv; data_at_ wsh t_struct_hmac_ctx_st (Vptr cb cofs);
   data_at_ Tsh (tarray tuchar 64) (Vptr ckb ckoff)))

     (Ssequence
                 (Scall None
                    (Evar _SHA256_Init
                       (Tfunction
                          (Tcons (tptr (Tstruct _SHA256state_st noattr)) Tnil)
                          tvoid cc_default))
                    [Eaddrof
                       (Efield
                          (Ederef
                             (Etempvar _ctx
                                (tptr (Tstruct _hmac_ctx_st noattr)))
                             (Tstruct _hmac_ctx_st noattr)) _md_ctx
                          (Tstruct _SHA256state_st noattr))
                       (tptr (Tstruct _SHA256state_st noattr))])
                 (Ssequence
                    (Scall None
                       (Evar _SHA256_Update
                          (Tfunction
                             (Tcons (tptr (Tstruct _SHA256state_st noattr))
                                (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                             tvoid cc_default))
                       [Eaddrof
                          (Efield
                             (Ederef
                                (Etempvar _ctx
                                   (tptr (Tstruct _hmac_ctx_st noattr)))
                                (Tstruct _hmac_ctx_st noattr)) _md_ctx
                             (Tstruct _SHA256state_st noattr))
                          (tptr (Tstruct _SHA256state_st noattr));
                       Etempvar _key (tptr tuchar); Etempvar _len tint])
                    (Ssequence
                       (Scall None
                          (Evar _SHA256_Final
                             (Tfunction
                                (Tcons (tptr tuchar)
                                   (Tcons
                                      (tptr (Tstruct _SHA256state_st noattr))
                                      Tnil)) tvoid cc_default))
                          [Evar _ctx_key (tarray tuchar 64);
                          Eaddrof
                            (Efield
                               (Ederef
                                  (Etempvar _ctx
                                     (tptr (Tstruct _hmac_ctx_st noattr)))
                                  (Tstruct _hmac_ctx_st noattr)) _md_ctx
                               (Tstruct _SHA256state_st noattr))
                            (tptr (Tstruct _SHA256state_st noattr))])
                  (Scall None
                    (Evar _memset (Tfunction
                                    (Tcons (tptr tvoid)
                                      (Tcons tint (Tcons tuint Tnil)))
                                    (tptr tvoid) cc_default))
                    ((Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                       (Econst_int (Int.repr 32) tint) (tptr tuchar)) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 32) tint) :: nil)))))
  (normal_ret_assert  (PROP  ()
                  LOCAL  (temp _reset (Vint (Int.repr 1));
                  lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
                  lvar _pad (tarray tuchar 64) pad; temp _ctx (Vptr cb cofs);
                  temp _key (Vptr kb kofs); temp _len (Vint (Int.repr l));
                  gvars gv)
                  SEP  (data_at_ Tsh (tarray tuchar 64) pad;
                  data_at wsh t_struct_hmac_ctx_st HMS' (Vptr cb cofs);
                  data_at sh (tarray tuchar (Zlength key))
                      (map Vubyte key) (Vptr kb kofs);
                  data_at Tsh (tarray tuchar 64)
                      (map Vubyte (HMAC_SHA256.mkKey key))
                      (Vptr ckb ckoff); K_vector gv))).
Proof. intros. abbreviate_semax.
      (*call to SHA256_init*)
      freeze [0; 1; 4] FR1.
      unfold data_at_ at 1. unfold field_at_ at 1.
      simpl.
      Time unfold_field_at 1%nat. (*7.7*)
      rewrite (field_at_data_at wsh t_struct_hmac_ctx_st [StructField _md_ctx]).
      rewrite field_address_offset by auto with field_compatible.
      simpl. rewrite Ptrofs.add_zero.

      freeze [0;1] FR2.

      (*new: extract info from field_address as early as possible*)
      Time assert_PROP (isptr (field_address t_struct_hmac_ctx_st [StructField _md_ctx]
                          (Vptr cb cofs))) as FA_MDCTX by entailer!. (*2.9 versus 4.2*)
      Time assert_PROP (field_compatible t_struct_SHA256state_st [] (Vptr cb cofs)) as
         FCcb by entailer!. (*3.8*)

      freeze [0;2;3] FR3.
      Time forward_call (Vptr cb cofs, wsh). (* 4.3 versus 18 *)
       (*call to SHA256_Update*)
      thaw FR3.
      thaw FR2.
      thaw FR1.
      freeze [2;3;5;6] FR4.
      Time forward_call (@nil byte, key, Vptr cb cofs, wsh, Vptr kb kofs, sh, l, gv). (*4.5*)
      { unfold data_block.
        Time cancel. (*0.1*)
      }
      { 
        specialize Int.max_signed_unsigned.
        subst l. intro; split3; [ | | split3]; auto; omega.
      }
      rewrite sublist_same; trivial.

     (*call Final*)
     thaw FR4. simpl.
     freeze [2;3;5;6] FR5.
     freeze [0;1;2] FR6.
     unfold data_at_ at 1. unfold field_at_.
     Time rewrite field_at_data_at at 1. (* 4.2*)
     rewrite field_address_offset by auto with field_compatible.
     simpl. rewrite Ptrofs.add_zero.

     assert_PROP (field_compatible (Tarray tuchar 64 noattr) [] (Vptr ckb ckoff)) as FC_ctxkey.
     { Time entailer!. (*1.4*) }

     replace_SEP 1 (memory_block Tsh 64 (Vptr ckb ckoff)).
     { Time entailer!. (*2*) apply data_at_memory_block. }

     Time specialize (memory_block_split Tsh ckb (Ptrofs.unsigned ckoff) 32 32).
     rewrite Ptrofs.repr_unsigned.
     change (32+32) with 64.
     intros MBS; rewrite MBS; clear MBS; trivial.
     2:{ destruct (Ptrofs.unsigned_range ckoff). split; try omega.
              red in FC_ctxkey. simpl in FC_ctxkey. omega. } 
     flatten_sepcon_in_SEP.

     thaw FR6.
     freeze [0;4] FR7.
     Time forward_call (key, Vptr ckb ckoff, Vptr cb cofs, wsh, Tsh, gv). (*3.3.versus 4.3*)
       
     (*call memset*)
     thaw FR7.
     unfold tarray.
     freeze [0;1;2;3] FR8. (*everything except memory_block Ews 32 (Vptr ckb (Ptrofs.repr (Ptrofs.unsigned ckoff + 32))))*)
     Time forward_call (Tsh, Vptr ckb (Ptrofs.repr (Ptrofs.unsigned ckoff + 32)), 32, Int.zero). (*6.1 versus 6.9*)
     { Time entailer!. (*10.2*)
       unfold data_block. simpl. Time normalize. (*1.4*)
       unfold HMS.
       assert (SFL: Zlength  (SHA_256 key) = 32).
         rewrite <- functional_prog.SHA_256'_eq, Zlength_correct, length_SHA256'. reflexivity.
       assert (LK64: Zlength (HMAC_SHA256.mkKey key) = 64).
         unfold HMAC_SHA256.mkKey.
         remember (Zlength key >? Z.of_nat SHA256.BlockSize).
         destruct b; rewrite Zlength_correct, zeroPad_BlockSize. reflexivity.
                     unfold SHA256.Hash. rewrite length_SHA256'. unfold SHA256.DigestLength, SHA256.BlockSize. omega.
         reflexivity. apply Nat2Z.inj_le.
         specialize (Zgt_cases (Zlength key) (Z.of_nat SHA256.BlockSize)). rewrite <- Heqb. rewrite Zlength_correct; trivial.
       unfold tarray.
       rewrite (split2_data_at_Tarray_tuchar Tsh 64 32); repeat rewrite Zlength_map; trivial; try omega.
       unfold HMAC_SHA256.mkKey.
       remember (Zlength key >? Z.of_nat SHA256.BlockSize).
       destruct b.
       2:{ specialize (Zgt_cases (Zlength key) (Z.of_nat SHA256.BlockSize)).
                rewrite <- Heqb. intro Hx; simpl in Hx; omega.
       }
       clear Heqb.
       unfold HMAC_SHA256.zeroPad. repeat rewrite map_app.
       assert (LHash: Zlength (SHA256.Hash key) = 32).
         unfold SHA256.Hash. rewrite Zlength_correct, length_SHA256'; reflexivity.
       autorewrite with sublist. rewrite LHash.
       unfold SHA256.BlockSize.
       replace (length (SHA256.Hash key)) with 32%nat
         by (apply Nat2Z.inj; rewrite <- Zlength_correct, LHash; reflexivity).
       change (64-32)%nat with (Z.to_nat 32).
       autorewrite with sublist.
       change (64 - 32) with 32.
       fold Int.zero.
       rewrite field_address0_offset by auto with field_compatible. simpl.
       change (Ptrofs.repr (Ptrofs.unsigned ckoff + 32))
             with (Ptrofs.add ckoff (Ptrofs.repr 32)). (*rewrite Z.add_0_l.*)
       Time cancel. (*0.6*)
       thaw FR8. Time cancel.
       unfold data_block, SHA256.Hash, tarray. rewrite functional_prog.SHA_256'_eq, SFL. simpl.
       Time entailer!. (*2.1*)
       thaw FR5.
       unfold data_at_, field_at_, tarray, data_block.
       unfold_data_at 2%nat. simpl. Time cancel. (*0.7*)
       Time (normalize; cancel). (*0.6*)
       rewrite field_at_data_at, field_address_offset by auto with field_compatible.
       rewrite field_at_data_at, field_address_offset by auto with field_compatible.
       Time entailer!. (*0.1*)
  }
Time Qed. (*31.3 secs versus 58 secs*)

Lemma Init_part1_len_le_j Espec (kb ckb cb: block) (kofs ckoff cofs:ptrofs)
      l wsh sh (key: list byte) gv pad
      (HMS' : reptype t_struct_hmac_ctx_st): forall
(Hwsh: writable_share wsh)
(Hsh: readable_share sh)
(KL1 : l = Zlength key)
(KL2 : 0 < l <= Int.max_signed)
(KL3 : l * 8 < two_p 64)
(KHMS : HMS' = HMS)
(FC_ctx : field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs))
(FC_md_ctx : field_compatible t_struct_hmac_ctx_st [StructField _md_ctx]
              (Vptr cb cofs))
(FC_cxtkey : field_compatible (Tarray tuchar 64 noattr) [] (Vptr ckb ckoff))
(ge_64_l : 64 >= l),
@semax CompSpecs Espec
       (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs nil)
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr 64)); temp _reset (Vint (Int.repr 1));
   lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
   lvar _pad (tarray tuchar 64) pad; temp _ctx (Vptr cb cofs);
   temp _key (Vptr kb kofs); temp _len (Vint (Int.repr l));
   gvars gv)
   SEP  (data_at sh (tarray tuchar (Zlength key)) (map Vubyte key)
        (Vptr kb kofs); data_at_ Tsh (tarray tuchar 64) pad;
   K_vector gv; data_at_ wsh t_struct_hmac_ctx_st (Vptr cb cofs);
   data_at_ Tsh (tarray tuchar 64) (Vptr ckb ckoff)))


            (Ssequence
              (Scall None
                (Evar _memcpy (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                ((Evar _ctx_key (tarray tuchar 64)) ::
                 (Etempvar _key (tptr tuchar)) :: (Etempvar _len tint) ::
                 nil))
              (Scall None
                (Evar _memset (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons tint (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                ((Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                   (Etempvar _len tint) (tptr tuchar)) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Ebinop Osub (Esizeof (tarray tuchar 64) tuint)
                   (Etempvar _len tint) tuint) :: nil)))
  (normal_ret_assert (PROP  ()
                  LOCAL  (temp _reset (Vint (Int.repr 1));
                  lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
                  lvar _pad (tarray tuchar 64) pad; temp _ctx (Vptr cb cofs);
                  temp _key (Vptr kb kofs); temp _len (Vint (Int.repr l));
                  gvars gv)
                  SEP  (data_at_ Tsh (tarray tuchar 64) pad;
                  data_at wsh t_struct_hmac_ctx_st HMS' (Vptr cb cofs);
                  data_at sh (tarray tuchar (Zlength key))
                      (map Vubyte key) (Vptr kb kofs);
                  data_at Tsh (tarray tuchar 64)
                      (map Vubyte (HMAC_SHA256.mkKey key))
                      (Vptr ckb ckoff); K_vector gv))).
Proof. intros.
     (*call to memcpy*)
     freeze [1; 2; 3] FR1.
     unfold data_at_.
     Time forward_call ((sh, Tsh), Vptr ckb ckoff,
             Vptr kb kofs, mkTrep (Tarray tuchar (Zlength key) noattr)
                     (map Vubyte key), l). (*2 versus 4.4*)
     { unfold tarray. unfold field_at_ at 1. rewrite field_at_data_at.
       rewrite field_address_offset by auto with field_compatible; simpl. rewrite Ptrofs.add_zero.
       rewrite (split2_data_at_Tarray_tuchar _ _ l); trivial. 2: omega.
       rewrite sepcon_comm.
       rewrite sepcon_assoc.
       apply sepcon_derives. eapply derives_trans. apply data_at_memory_block.
           simpl. rewrite Z.max_r. rewrite Z.mul_1_l.  apply derives_refl. omega.
       Time cancel. (*0.1 versus 2.4*) }
     { simpl. specialize Int.max_signed_unsigned. rewrite Z.max_r, Z.mul_1_l by omega.
      split ; [ | split3]; auto; omega. }
     unfold tarray.
     remember (64 - l) as l64.
     remember (map Vubyte key) as KCONT.

     (*call memset*)
     freeze [0;1;3] FR2.
     Time forward_call (Tsh, Vptr ckb (Ptrofs.add ckoff (Ptrofs.repr (Zlength key))), l64, Int.zero). (*6.4 versus 10.4*)
     { (*Issue: this side condition is NEW*)
       apply prop_right. unfold Ptrofs.of_ints, Ptrofs.of_int, Ptrofs.to_int. normalize.
       rewrite <- KL1, Heql64. split; trivial. }
     { rewrite <- KL1.
       rewrite sepcon_comm. Time apply sepcon_derives; [ | cancel]. (*0.1 versus 1.2*)
       unfold at_offset. simpl.
         eapply derives_trans; try apply data_at_memory_block.
               rewrite sizeof_Tarray. trivial.
       rewrite field_address0_offset by auto with field_compatible.
       simpl. rewrite Z.add_0_l, Z.mul_1_l;  apply derives_refl.
       apply Z.max_r. omega. }
     { split; auto. rep_omega. }

     Time entailer!. (*3.5 versus 6.2*)
     thaw FR2. thaw FR1. Time cancel. (*1.2 penalty*)
     rewrite (split2_data_at_Tarray_tuchar Tsh 64 (Zlength key));
       try repeat rewrite Zlength_map; try rewrite Zlength_correct, mkKey_length;
     trivial. 2: omega.
     unfold at_offset.
     unfold HMAC_SHA256.mkKey. remember (64 - Zlength key) as SF. simpl.
       remember (Zlength key >? 64).
       destruct b. symmetry in Heqb; apply Zgt_is_gt_bool in Heqb. omega.
       unfold HMAC_SHA256.zeroPad. repeat rewrite map_app.
     autorewrite with sublist.
     assert (XX: (SHA256.BlockSize - length key = Z.to_nat SF)%nat).
          subst SF. rewrite Zlength_correct, Z2Nat.inj_sub, Nat2Z.id. reflexivity. omega.
     rewrite XX(*, HeqKCONT*).
     repeat rewrite map_list_repeat.
     rewrite sublist_same; trivial. (*subst l64 l.*)
     change (Tarray tuchar 64 noattr) with (tarray tuchar 64).
     rewrite field_address0_offset by auto with field_compatible. simpl. rewrite Z.mul_1_l.
     change (0 + Zlength key) with (Zlength key).
     Time cancel. apply derives_refl.
     rewrite Zlength_list_repeat', Z2Nat.id; omega.
Time Qed. (*10 secs versus 18*)
