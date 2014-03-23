Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.sha_lemmas2.
Require Import sha.verif_sha_final2.
Local Open Scope logic.


Definition sha_final_epilog :=
              (Ssequence
                          (Scall None
                            (Evar _sha256_block_data_order (Tfunction
                                                             (Tcons
                                                               (tptr t_struct_SHA256state_st)
                                                               (Tcons
                                                                 (tptr tvoid)
                                                                 Tnil))
                                                             tvoid))
                            ((Etempvar _c (tptr t_struct_SHA256state_st)) ::
                             (Etempvar _p (tptr tuchar)) :: nil))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _c (tptr t_struct_SHA256state_st))
                                  t_struct_SHA256state_st) _num tuint)
                              (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Scall None
                                (Evar _memset (Tfunction
                                                (Tcons (tptr tvoid)
                                                  (Tcons tint
                                                    (Tcons tuint Tnil)))
                                                (tptr tvoid)))
                                ((Etempvar _p (tptr tuchar)) ::
                                 (Econst_int (Int.repr 0) tint) ::
                                 (Ebinop Omul (Econst_int (Int.repr 16) tint)
                                   (Econst_int (Int.repr 4) tint) tint) ::
                                 nil))
           (Ssequence final_loop (Sreturn None))))).

Lemma sha_final_part3:
forall (Espec : OracleKind) (md c : val) (shmd : share)
  (hashed lastblock: list int) msg
 (Hshmd: writable_share shmd),
 (LBLOCKz | Zlength hashed) ->
 Zlength lastblock = LBLOCKz ->
 generate_and_pad msg = hashed++lastblock ->
semax
  (initialized _cNl (initialized _cNh Delta_final_if1))
  (PROP  ()
   LOCAL  (`(eq (offset_val (Int.repr 40) c)) (eval_id _p);
   `(eq md) (eval_id _md); `(eq c) (eval_id _c))
   SEP 
   (`(data_block Tsh (intlist_to_Zlist lastblock)
                 (offset_val (Int.repr 40) c));
   `(array_at tuint Tsh
       (ZnthV tuint (map Vint (hash_blocks init_registers hashed))) 0 8 c);
   `(field_at_ Tsh t_struct_SHA256state_st _Nl c);
   `(field_at_ Tsh t_struct_SHA256state_st _Nh c);
   `(field_at_ Tsh t_struct_SHA256state_st _num c); K_vector;
   `(memory_block shmd (Int.repr 32) md)))
  sha_final_epilog
  (function_body_ret_assert tvoid
     (PROP  ()
      LOCAL ()
      SEP  (K_vector; `(data_at_ Tsh t_struct_SHA256state_st c);
      `(data_block shmd (SHA_256 msg) md)))).
Proof.
intros.
unfold sha_final_epilog.
simplify_Delta; abbreviate_semax.
forward_call (* sha256_block_data_order (c,p); *)
  (hashed, lastblock, c, (offset_val (Int.repr 40) c), Tsh).
entailer!.
normalize.
replace_SEP 2%Z  (K_vector).
entailer!.
unfold data_block.
simpl. rewrite prop_true_andp by apply isbyte_intlist_to_Zlist.
rewrite <- H1.
forward. (* c->num=0; *)
forward_call (* memset (p,0,SHA_CBLOCK); *) 
  (Tsh, (offset_val (Int.repr 40) c), 64%Z, Int.zero).
entailer!. 
 fold t_struct_SHA256state_st.
 rewrite (memory_block_array_tuchar _ 64%Z) by Omega1.
 rewrite Zlength_intlist_to_Zlist, H0. change (4*LBLOCKz) with 64.
 cancel.
autorewrite with subst.
replace_SEP 0%Z (`(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0 64
          (offset_val (Int.repr 40) c))).
entailer!.
fold t_struct_SHA256state_st.
pose proof (length_hash_blocks (generate_and_pad msg)).

replace Delta with
   (initialized _cNl (initialized _cNh Delta_final_if1))
 by (simplify_Delta; reflexivity).
eapply semax_pre; [ | apply final_part4; auto].
entailer!.
apply length_hash_blocks; auto.
rewrite length_generate_and_pad; apply roundup_divide; computable.
Qed.

Lemma final_part5:
forall (hashed: list int) (dd:list Z) (hashed': list int) (dd' : list Z) (pad : Z) (hi' lo' : list Z)
  (hi lo : int) c_,
 (LBLOCKz | Zlength hashed) ->
(Zlength dd < CBLOCKz) ->
(length dd' + 8 <= CBLOCK)%nat ->
(0 <= pad < 8)%Z ->
(LBLOCKz | Zlength hashed') ->
intlist_to_Zlist hashed' ++ dd' =
intlist_to_Zlist hashed ++ dd ++ [128%Z] ++ map Int.unsigned (zeros pad) ->
length hi' = 4%nat ->
length lo' = 4%nat ->
isptr c_ ->
hi' = intlist_to_Zlist [hi] /\ lo' = intlist_to_Zlist [lo] ->
array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr lo'))) 0 4
  (offset_val (Int.repr 100) c_) *
array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr hi'))) 0 4
  (offset_val (Int.repr 96) c_) *
array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0
  (Z.of_nat CBLOCK - 8 - Zlength dd')
  (offset_val (Int.repr (Zlength dd' + 40)) c_) *
array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd'))) 0 (Zlength dd')
  (offset_val (Int.repr 40) c_)
|-- array_at tuchar Tsh
      (ZnthV tuchar
         (map Vint
            (map Int.repr dd' ++
             zeros (Z.of_nat CBLOCK - 8 - Zlength dd') ++
             map Int.repr (hi' ++ lo')))) 0 64 (offset_val (Int.repr 40) c_).
Proof.
intros until c_.
intros H4 H3 H0 H1 H2 H5 Lhi Llo Pc_ Hhilo.
 rewrite (split_array_at (Zlength dd') tuchar Tsh _ 0 64)
  by (clear - H0; rewrite Zlength_correct; change CBLOCK with 64%nat in H0;
  omega).
 rewrite (split_array_at 56 tuchar Tsh _ (Zlength dd') 64)
  by (clear - H0; rewrite Zlength_correct; change CBLOCK with 64%nat in H0;
  omega).
 rewrite (split_array_at 60 tuchar Tsh _ 56 64) by omega.
 replace (offset_val (Int.repr 100) c_) with
            (offset_val (Int.repr (sizeof tuchar * 60)) (offset_val (Int.repr 40) c_))
  by (rewrite offset_offset_val; destruct c_; reflexivity).
 replace (offset_val (Int.repr 96) c_) with
            (offset_val (Int.repr (sizeof tuchar * 56)) (offset_val (Int.repr 40) c_))
  by (rewrite offset_offset_val; destruct c_; reflexivity).
 replace (offset_val (Int.repr (Zlength dd' + 40)) c_) with
            (offset_val (Int.repr (sizeof tuchar * Zlength dd')) (offset_val (Int.repr 40) c_))
  by (change (sizeof tuchar) with 1%Z; rewrite Z.mul_1_l; rewrite offset_offset_val; rewrite Int.add_commut, add_repr; reflexivity).
 forget (offset_val (Int.repr 40) c_) as cc.
 repeat rewrite <- offset_val_array_at.
 apply derives_trans with
  (array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd'))) 0 (Zlength dd') cc *
   array_at tuchar Tsh (fun _ : Z => Vint Int.zero) (Zlength dd' + 0)
   (Zlength dd' + (Z.of_nat CBLOCK - 8 - Zlength dd')) cc *
   array_at tuchar Tsh (fun i : Z => ZnthV tuchar (map Vint (map Int.repr hi')) (i - 56)) 
      56 60 cc *
  array_at tuchar Tsh (fun i : Z => ZnthV tuchar (map Vint (map Int.repr lo')) (i - 60)) 
      60 64 cc);
  [solve [cancel] | ].
 rewrite Z.add_0_r.
 replace (Zlength dd' + (Z.of_nat CBLOCK - 8 - Zlength dd'))%Z
  with 56%Z by (change (Z.of_nat CBLOCK) with 64%Z; clear; omega).
 assert (Zlength dd' >= 0)%Z by (rewrite Zlength_correct; omega).
 assert (Zlength dd' = Z.of_nat (length (map Vint (map Int.repr dd')))).
 rewrite Zlength_correct; repeat rewrite map_length; reflexivity.
 assert (Z.of_nat CBLOCK - 8 - Z.of_nat (length dd') >= 0)%Z.
 clear - H0. apply Nat2Z.inj_le in H0. rewrite Nat2Z.inj_add in H0.
  change (Z.of_nat 8) with 8 in H0. omega.
 repeat rewrite sepcon_assoc;
 repeat apply sepcon_derives; apply derives_refl';
 apply equal_f; try apply array_at_ext; intros;
 unfold ZnthV; repeat rewrite if_false by omega.
+ repeat rewrite map_app.
   rewrite app_nth1; [reflexivity | ].
 apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega; omega.
+ repeat rewrite map_app.
   rewrite app_nth2. rewrite app_nth1.
  rewrite nth_map_zeros. auto.
  rewrite Nat2Z.inj_sub by Omega1. Omega1.
  rewrite (map_length _ (zeros _)).
  rewrite length_zeros.
  apply Nat2Z.inj_lt; rewrite Nat2Z.inj_sub; Omega1.
  Omega1.
+ repeat rewrite map_app.
   rewrite <- app_ass.
   rewrite app_nth2. rewrite app_nth1.
   f_equal.    rewrite app_length.  
   repeat rewrite map_length; rewrite map_length in H6.
   rewrite length_zeros.
   rewrite H6. Omega1.
  rewrite app_length; rewrite (map_length _ (zeros _)); rewrite length_zeros.
  rewrite H6. repeat rewrite map_length.
  rewrite Lhi.
    change (Z.of_nat CBLOCK - 8)%Z with 56%Z. 
  apply Nat2Z.inj_lt; try omega.
  rewrite Nat2Z.inj_sub; try Omega1.
  rewrite H6; repeat rewrite app_length; repeat rewrite map_length;
   rewrite length_zeros.
  Omega1.
+
assert (length
  (map Vint
     ((map Int.repr dd' ++ zeros (Z.of_nat CBLOCK - 8 - Zlength dd')) ++
      map Int.repr hi')) = 60%nat).
  rewrite map_length.
 repeat rewrite app_length.
 repeat rewrite map_length.
 rewrite length_zeros.
 rewrite Lhi, Zlength_correct.
 rewrite Z2Nat.inj_sub by omega.
 rewrite Nat2Z.id.
 rewrite Z2Nat.inj_sub by omega.
 rewrite Nat2Z.id. change CBLOCK with 64%nat.
 change (Z.to_nat 8) with 8%nat.
 clear- H0; change CBLOCK with 64%nat in H0; omega.
  rewrite (map_app Int.repr).
  repeat rewrite <- app_ass.
  rewrite map_app.
  rewrite app_nth2.
 rewrite H9.
  rewrite Z2Nat.inj_sub by omega; auto.
 rewrite H9.
 clear - H8. change 60%nat with (Z.to_nat 60).
 apply Z2Nat.inj_le; omega.
Qed.

Lemma final_part2:
forall (Espec : OracleKind) (hashed : list int) (md c : val) (shmd : share),
writable_share shmd ->
name _md ->
name _c ->
name _p ->
name _n ->
name _cNl ->
name _cNh ->
forall (hi lo : int) (dd : list Z),
(LBLOCKz | Zlength hashed) ->
((Zlength hashed * 4 + Zlength dd)*8)%Z = hilo hi lo ->
(Zlength dd < CBLOCKz) ->
 (Forall isbyteZ dd) ->
forall (hashed': list int) (dd' : list Z) (pad : Z),
 (Forall isbyteZ dd') ->
 (pad=0%Z \/ dd'=nil) ->
(length dd' + 8 <= CBLOCK)%nat ->
(0 <= pad < 8)%Z ->
(LBLOCKz | Zlength hashed') ->
intlist_to_Zlist hashed' ++ dd' =
intlist_to_Zlist hashed ++ dd ++ [128%Z] ++ map Int.unsigned (zeros pad) ->
forall p0 : val,
semax Delta_final_if1
  (PROP  ()
   LOCAL 
   (`(eq (force_val (sem_add_pi tuchar p0 (Vint (Int.repr (16 * 4 - 8))))))
      (eval_id _p); `(eq (Vint (Int.repr (Zlength dd')))) (eval_id _n);
   `(eq p0) (`(offset_val (Int.repr 40)) (`force_ptr (eval_id _c)));
   `(eq md) (eval_id _md); `(eq c) (eval_id _c))
   SEP 
   (`(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0
        (Z.of_nat CBLOCK - 8 - Zlength dd')
        (offset_val (Int.repr (40 + Zlength dd')) c));
   `(array_at tuint Tsh
       (ZnthV tuint (map Vint (hash_blocks init_registers hashed'))) 0 8 c);
   `(field_at Tsh t_struct_SHA256state_st _Nl (Vint lo) c);
   `(field_at Tsh t_struct_SHA256state_st _Nh (Vint hi) c);
   `(array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd'))) 0 (Zlength dd')
       (offset_val (Int.repr 40) c));
   `(array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd'))) (Z.of_nat CBLOCK - 8)
       64 (offset_val (Int.repr 40) c));
   `(field_at_ Tsh t_struct_SHA256state_st _num c); K_vector;
   `(memory_block shmd (Int.repr 32) md)))
  (Ssequence
     (Sset _cNh
        (Efield
           (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
              t_struct_SHA256state_st) _Nh tuint))
     (Ssequence
        (Ssequence
           (Scall None
              (Evar ___builtin_write32_reversed
                 (Tfunction (Tcons (tptr tuint) (Tcons tuint Tnil)) tvoid))
              [Ecast (Etempvar _p (tptr tuchar)) (tptr tuint),
              Etempvar _cNh tuint])
           (Sset _p
              (Ebinop Oadd (Etempvar _p (tptr tuchar))
                 (Econst_int (Int.repr 4) tint) (tptr tuchar))))
        (Ssequence
           (Sset _cNl
              (Efield
                 (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                    t_struct_SHA256state_st) _Nl tuint))
           (Ssequence
              (Ssequence
                 (Scall None
                    (Evar ___builtin_write32_reversed
                       (Tfunction (Tcons (tptr tuint) (Tcons tuint Tnil))
                          tvoid))
                    [Ecast (Etempvar _p (tptr tuchar)) (tptr tuint),
                    Etempvar _cNl tuint])
                 (Sset _p
                    (Ebinop Oadd (Etempvar _p (tptr tuchar))
                       (Econst_int (Int.repr 4) tint) (tptr tuchar))))
              (Ssequence
                 (Sset _p
                    (Ebinop Osub (Etempvar _p (tptr tuchar))
                       (Ebinop Omul (Econst_int (Int.repr 16) tint)
                          (Econst_int (Int.repr 4) tint) tint) (tptr tuchar)))
                 (Ssequence
                    (Scall None
                       (Evar _sha256_block_data_order
                          (Tfunction
                             (Tcons (tptr t_struct_SHA256state_st)
                                (Tcons (tptr tvoid) Tnil)) tvoid))
                       [Etempvar _c (tptr t_struct_SHA256state_st),
                       Etempvar _p (tptr tuchar)])
                    (Ssequence
                       (Sassign
                          (Efield
                             (Ederef
                                (Etempvar _c (tptr t_struct_SHA256state_st))
                                t_struct_SHA256state_st) _num tuint)
                          (Econst_int (Int.repr 0) tint))
                       (Ssequence
                             (Scall None
                                (Evar _memset
                                   (Tfunction
                                      (Tcons (tptr tvoid)
                                         (Tcons tint (Tcons tuint Tnil)))
                                      (tptr tvoid)))
                                [Etempvar _p (tptr tuchar),
                                Econst_int (Int.repr 0) tint,
                                Ebinop Omul (Econst_int (Int.repr 16) tint)
                                  (Econst_int (Int.repr 4) tint) tint])
                          (Ssequence
                             final_loop
                             (Sreturn None))))))))))
  (function_body_ret_assert tvoid
     (PROP  ()
      LOCAL ()
      SEP  (K_vector; `(data_at_ Tsh t_struct_SHA256state_st c);
      `(data_block shmd
          (intlist_to_Zlist
             (hash_blocks init_registers
                (generate_and_pad
                   (intlist_to_Zlist hashed ++ dd))))
          md)))).
Proof.
 intros Espec hashed md c shmd H md_ c_ p n cNl cNh
 hi lo dd H4 H7 H3 DDbytes hashed' dd' pad 
 DDbytes' PAD H0 H1 H2 H5 p0.
 pose (hibytes := Basics.compose force_int (ZnthV tuchar (map Vint (map Int.repr (intlist_to_Zlist [hi]))))).
 pose (lobytes := Basics.compose force_int (ZnthV tuchar (map Vint (map Int.repr (intlist_to_Zlist [lo]))))).
 rewrite (split_array_at 60%Z tuchar Tsh _ (Z.of_nat CBLOCK - 8)%Z 64%Z)
  by (change (Z.of_nat CBLOCK) with 64%Z; split; computable).
 forward. (* cNh=c->Nh; *)
 repeat apply -> seq_assoc.
 forward_call (* (void)HOST_l2c(cNh,p); *)
    (offset_val (Int.repr 56) (offset_val (Int.repr 40) c),
                         Tsh, hibytes).
 rewrite (Z.add_comm 40).
 entailer!.
 destruct c; try (contradiction Pc); simpl. f_equal; rewrite Int.add_assoc; rewrite mul_repr; rewrite add_repr; reflexivity.
 unfold hibytes.
 symmetry; rewrite (nth_big_endian_integer 0 [hi] hi) at 1 by reflexivity.
 f_equal; extensionality z; unfold Basics.compose.
 f_equal; f_equal.
 change (Z.of_nat 0 * 4)%Z with 0%Z. clear; omega.
 pull_left   (array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd')))
            (Z.of_nat CBLOCK - 8) 60 (offset_val (Int.repr 40) c)) .
 repeat rewrite sepcon_assoc.
 apply sepcon_derives; [ | cancel_frame].
 change 40%Z with (sizeof tuchar * 40)%Z at 1.
 rewrite <- offset_val_array_at.
 change (Int.repr 4) with (Int.repr (sizeof (tarray tuchar 4))).
 rewrite memory_block_typed by reflexivity.
 simpl_data_at.
 change (40+56)%Z with (sizeof tuchar * (40+56))%Z.
 rewrite <- offset_val_array_at.
 change (40+56+4)%Z with (40+60)%Z.
 change (40 + (Z.of_nat CBLOCK - 8))%Z with (40 + 56 + 0)%Z.
 apply derives_refl'; apply equal_f; apply array_at_ext.
 intros. unfold ZnthV. rewrite if_false by omega.
 rewrite if_false by omega.
 rewrite nth_overflow.
 rewrite nth_overflow. auto.
 simpl length.
 rewrite Z2Nat.inj_sub by omega. omega.
clear - H0 H9.
 rewrite map_length in *.
 change CBLOCK with 64%nat in H0.
 assert (56 <= i-40)%Z by omega.
 apply Z2Nat.inj_le in H; try omega.
 change (Z.to_nat 56) with 56%nat in H; rewrite map_length; omega.
 forward. (* p += 4; *)
 entailer!.
 forward. (* cNl=c->Nl; *)
 repeat apply -> seq_assoc. (* delete me *)
 forward_call (* (void)HOST_l2c(cNl,p); *)
 (offset_val (Int.repr 60) (offset_val (Int.repr 40) c), Tsh, lobytes).
 entailer!.
 destruct c; try (contradiction Pc); simpl.
 f_equal; repeat rewrite Int.add_assoc; f_equal.
 unfold lobytes.
 symmetry; rewrite (nth_big_endian_integer 0 [lo] lo) at 1 by reflexivity.
 f_equal; extensionality z; unfold Basics.compose.
 f_equal; f_equal.
 change (Z.of_nat 0 * 4)%Z with 0%Z. clear; omega.
 pull_left   (array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd')))
             60 64 (offset_val (Int.repr 40) c)) .
 repeat rewrite sepcon_assoc.
 apply sepcon_derives; [ | cancel_frame].
 change 40%Z with (sizeof tuchar * 40)%Z at 1.
 rewrite <- offset_val_array_at.
 change (Int.repr 4) with (Int.repr (sizeof (tarray tuchar 4))).
 rewrite memory_block_typed by reflexivity.
 simpl_data_at.
 change (40+60)%Z with (sizeof tuchar * (40+60))%Z.
 rewrite <- offset_val_array_at.
 change (40+60+0)%Z with (40+60)%Z.
 change (40 + 60+4)%Z with (40 + 64)%Z.
 apply derives_refl'; apply equal_f; apply array_at_ext.
 intros. unfold ZnthV. rewrite if_false by omega.
 rewrite if_false by omega.
 rewrite nth_overflow.
 rewrite nth_overflow. auto.
 simpl length.
 rewrite Z2Nat.inj_sub by omega. omega.
clear - H0 H10.
 rewrite map_length in *.
 change CBLOCK with 64%nat in H0.
 assert (60 <= i-40)%Z by omega.
 apply Z2Nat.inj_le in H; try omega.
 change (Z.to_nat 60) with 60%nat in H; rewrite map_length; omega.
 autorewrite with subst.
 normalize.
 forward. (* p += 4; *)
 entailer!. destruct c_; try (contradiction Pc_); apply I.
 forward. (*   p -= SHA_CBLOCK; *)
 entailer!. destruct c_; try (contradiction Pc_); apply I.
 simpl. normalize.
 simpl force_val2. normalize.
 replace (array_at tuchar Tsh (cVint lobytes) 0 4) with 
     (array_at tuchar Tsh  (ZnthV tuchar
                (map Vint (map Int.repr (intlist_to_Zlist [lo])))) 0 4).
Focus 2. apply array_at_ext; intros; unfold cVint, lobytes, ZnthV, Basics.compose; if_tac; try reflexivity.
omega.
rewrite (nth_map' Vint Vundef Int.zero)
 by (simpl length; apply Nat2Z.inj_lt;
       rewrite Z2Nat.id; change (Z.of_nat 4) with 4%Z; omega).
 reflexivity.
 replace (array_at tuchar Tsh (cVint hibytes) 0 4) with 
     (array_at tuchar Tsh  (ZnthV tuchar
                (map Vint (map Int.repr (intlist_to_Zlist [hi])))) 0 4).
Focus 2. apply array_at_ext; intros; unfold cVint, hibytes, ZnthV, Basics.compose; if_tac; try reflexivity.
omega.
rewrite (nth_map' Vint Vundef Int.zero)
 by (simpl length; apply Nat2Z.inj_lt;
       rewrite Z2Nat.id; change (Z.of_nat 4) with 4%Z; omega).
 reflexivity.
clear lobytes hibytes.
normalize.
pose (lastblock := (
         (map Int.repr dd' ++ zeros (Z.of_nat CBLOCK - 8 - Zlength dd')
          ++  map Int.repr (intlist_to_Zlist [hi,lo])))).
assert (H10: length lastblock = CBLOCK).
unfold lastblock; repeat rewrite app_length.
rewrite length_zeros; simpl.
clear - H0.
rewrite Zlength_correct. repeat rewrite Z2Nat.inj_sub by omega.
repeat rewrite Nat2Z.id. simpl Z.to_nat. rewrite map_length; omega.
assert (BYTESlastblock: Forall isbyteZ (map Int.unsigned lastblock)). {
 unfold lastblock.
 repeat rewrite map_app.
 repeat rewrite Forall_app.
 repeat split; auto.
 apply Forall_isbyteZ_unsigned_repr; auto.
 apply isbyte_zeros.
 apply isbyte_intlist_to_Zlist'.
}
unfold POSTCONDITION, abbreviate.
fold (SHA_256 (intlist_to_Zlist hashed ++ dd)).
pose (lastblock' := Zlist_to_intlist (map Int.unsigned lastblock)).
eapply semax_pre; [ | simple apply (sha_final_part3 Espec md c shmd hashed' lastblock'); auto].
* entailer!.
 + destruct c_; try (contradiction Pc_); simpl;
     f_equal; rewrite Int.sub_add_opp;
     repeat rewrite Int.add_assoc; f_equal; reflexivity.
 + 
unfold lastblock', data_block.
simpl.
rewrite prop_true_andp by apply isbyte_intlist_to_Zlist.
rewrite Zlist_to_intlist_to_Zlist; [ |rewrite map_length; rewrite H10; exists LBLOCK; reflexivity | assumption].
rewrite Forall_isbyte_repr_unsigned.
rewrite (Zlength_correct (map _ lastblock)). try rewrite map_length; rewrite H10.
change (Z.of_nat CBLOCK) with 64%Z at 2.
change (intlist_to_Zlist [hi, lo])
  with (intlist_to_Zlist [hi] ++intlist_to_Zlist [lo]).
apply (final_part5 hashed dd hashed' dd' pad (intlist_to_Zlist [hi]) (intlist_to_Zlist [lo]) hi lo);
  auto. 
* unfold lastblock'.
apply Zlength_length; auto; apply length_Zlist_to_intlist.
rewrite map_length; assumption.
*
apply intlist_to_Zlist_inj.
rewrite (lastblock_lemma _ hashed' dd' pad hi lo); auto.
2: repeat rewrite app_ass; apply H5.
2: rewrite <- H7; f_equal; rewrite initial_world.Zlength_app,
        Zlength_intlist_to_Zlist, Z.mul_comm; reflexivity.
2: apply Forall_app; split; auto;apply isbyte_intlist_to_Zlist.
rewrite (app_ass _ dd); rewrite <- H5.
rewrite app_ass; rewrite intlist_to_Zlist_app.
f_equal.
unfold lastblock'.
rewrite Zlist_to_intlist_to_Zlist;
 [  | rewrite map_length, H10; exists LBLOCK;reflexivity | auto].
unfold lastblock; repeat rewrite map_app.
f_equal.
symmetry; apply map_unsigned_repr_isbyte; auto.
f_equal.
f_equal.
f_equal.
clear dependent p1. clear dependent p2. clear p0 p3.
clear Delta POSTCONDITION MORE_COMMANDS.
clear DDbytes DDbytes'.
clear lastblock'.
clear dependent lastblock.
clear dependent hi; clear lo.
clear dependent shmd.
destruct PAD; subst; simpl in *.
rewrite Z.sub_0_r.
replace (Zlength (intlist_to_Zlist hashed ++ dd) + 9)
  with (Zlength (intlist_to_Zlist hashed') + Zlength dd' + 8). 
{
 clear - H0 H2.
 apply Nat2Z.inj_le in H0. rewrite Nat2Z.inj_add in H0.
 change (Z.of_nat 8) with 8 in H0. rewrite <- Zlength_correct in H0.
 destruct H2 as [n ?].
 rewrite Zlength_intlist_to_Zlist. rewrite H.
 rewrite Z.mul_comm. rewrite <- Z.mul_assoc.
  change (Z.of_nat CBLOCK) with CBLOCKz in *.
  change (LBLOCKz * 4)%Z with CBLOCKz.
 rewrite <- Z.add_assoc.
 rewrite <- Z.sub_0_l.
 rewrite Zminus_mod.
 replace (0 mod CBLOCKz) with ((CBLOCKz + n * CBLOCKz) mod CBLOCKz).
 rewrite <- Zminus_mod.
 match goal with |- ?A mod _ = _ =>
    replace A with (CBLOCKz - 8 - Zlength dd') by omega
 end.
 rewrite Zmod_small by (rewrite Zlength_correct in *; omega).
 auto.
 rewrite Zplus_mod. 
 rewrite Zmult_mod. rewrite Z.mod_same by (intro Hx; inv Hx).
 rewrite Z.mul_0_r.
 rewrite Z.mod_0_l by (intro Hx; inv Hx).
  rewrite Z.mod_0_l by (intro Hx; inv Hx). auto.
}
{
 transitivity (Zlength (intlist_to_Zlist hashed ++ dd ++ [128]) + 8).
 rewrite <- H5.
 rewrite initial_world.Zlength_app; omega.
 rewrite <- app_ass.
 rewrite initial_world.Zlength_app.
 rewrite <- Z.add_assoc.
 reflexivity.
}
rewrite <- app_nil_end in H5.
rewrite Zlength_nil.
assert (Zlength dd + 1 + pad = CBLOCKz). {
 clear - H4  H3 H1 H2 H5.
 destruct H4 as [a H4]; destruct H2 as [b H2].
 apply (f_equal (@Zlength _)) in H5.
 rewrite Zlength_intlist_to_Zlist in H5. 
 rewrite H2 in H5. clear H2 hashed'.
 repeat rewrite initial_world.Zlength_app in H5.
 rewrite Zlength_intlist_to_Zlist in H5. 
 rewrite Zlength_cons, initial_world.Zlength_map,
 Zlength_zeros  in H5; try omega.
 unfold Z.succ in H5.
 rewrite H4 in H5.
 repeat rewrite (Z.mul_comm 4) in H5.
 repeat rewrite <- Z.mul_assoc in H5.
 change (LBLOCKz * 4)%Z with CBLOCKz in H5.
 replace (Zlength dd + (pad + 1)) with (Zlength dd + 1 + pad) in H5 by (clear; omega).
 assert (0 <= Zlength dd) by (rewrite Zlength_correct; clear; omega).
 forget (Zlength dd) as d; clear dd. clear hashed H4.
 assert ((b-a) * CBLOCKz = d + 1 + pad)%Z
 by (rewrite Z.mul_sub_distr_r; omega).
 clear H5.
 assert (0 < d + 1 + pad < 2 * CBLOCKz)
  by (change CBLOCKz with 64 in *; omega).
 forget (d+1+pad) as c. forget (b-a) as e.
 clear - H0 H2.
 subst c.
 change CBLOCKz with 64 in *.
 assert (0<e). 
 apply Zmult_lt_0_reg_r with 64; try omega.
 assert (e<2).
 apply Zmult_gt_0_lt_reg_r with 64; omega.
 assert (e=1) by omega; subst e; reflexivity.
}
transitivity (- (Zlength dd + 9) mod CBLOCKz - pad). {
 f_equal.
 rewrite initial_world.Zlength_app.
 rewrite <- Z.add_assoc.
 rewrite <- Z.sub_0_l.
 rewrite Zminus_mod.
 rewrite Zplus_mod.
 rewrite Zlength_intlist_to_Zlist. destruct H4 as [a H4].
 rewrite H4. rewrite Z.mul_comm. rewrite <- Z.mul_assoc.
 change (LBLOCKz * 4)%Z with CBLOCKz.
 rewrite Z_mod_mult. rewrite Z.add_0_l.
 rewrite Zmod_mod.
 rewrite <- Zminus_mod.
 rewrite Z.sub_0_l.
 auto.
}
replace (Zlength dd) with (CBLOCKz - (1+pad)) by omega.
replace (CBLOCKz - (1+pad) + 9) with (CBLOCKz + (8-pad)) by omega.
rewrite Z.mod_opp_l_nz.
2:intro Hx; inv Hx.
Focus 2. {
 rewrite Z.add_mod by (intro Hx; inv Hx).
 rewrite Z.mod_same by (intro Hx; inv Hx).
 rewrite Z.add_0_l. rewrite Z.mod_mod by (intro Hx; inv Hx).
 rewrite (Z.mod_small  (8 - pad)) by (change CBLOCKz with 64; omega).
 omega.
} Unfocus.
rewrite Z.add_mod by (intro Hx; inv Hx).
rewrite Z_mod_same by (change CBLOCKz with 64; omega).
rewrite Z.add_0_l.
rewrite Z.mod_mod by (change CBLOCKz with 64; omega).
rewrite Z.mod_small by (change CBLOCKz with 64; omega).
change (Z.of_nat CBLOCK) with CBLOCKz.
omega.
Qed.

