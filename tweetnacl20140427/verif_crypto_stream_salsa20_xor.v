Require Import VST.floyd.proofauto.
Local Open Scope logic.
Require Import Coq.Lists.List. Import ListNotations.
Require Import sha.general_lemmas.

Require Import tweetnacl20140427.split_array_lemmas.
Require Import ZArith.
Local Open Scope Z. 
From tweetnacl20140427
 Require Import tweetNaclBase Salsa20 verif_salsa_base 
      tweetnaclVerifiableC Snuffle spec_salsa 
     verif_crypto_stream_salsa20_xor1. 
Opaque Snuffle.Snuffle.

Definition Inv cInit mInit bInit k nonce x z Nonce K mcont zcont gv:=
(EX rounds:nat, EX m:_, EX zbytesR:list byte, EX srbytes:list byte,
 let r64 := (Z.of_nat rounds * 64)%Z in
 let c := offset_val r64 cInit in
 let b := Int64.sub bInit (Int64.repr r64) in
  (PROP  (0 <= r64 <= Int64.unsigned bInit /\ null_or_offset mInit r64 m
          /\ CONTENT SIGMA K mInit mcont zcont rounds zbytesR srbytes)
   LOCAL  (lvar _x (Tarray tuchar 64 noattr) x;
           lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
           temp _b (Vlong b); temp _n nonce; temp _k k; gvars gv)
   SEP (data_at Tsh (Tarray tuchar 16 noattr) (Bl2VL zbytesR) z;
     data_at_ Tsh (Tarray tuchar 64 noattr) x; Sigma_vector (gv _sigma);
     data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList Nonce) nonce;
     ThirtyTwoByte K k; 
     data_at Tsh (Tarray tuchar  (Z.of_nat rounds * 64) noattr) (Bl2VL srbytes) cInit;
     data_at_ Tsh (Tarray tuchar (Int64.unsigned bInit - Z.of_nat rounds * 64) noattr) c;
     message_at mcont mInit))).

Definition IfPost z x b Nonce K mCont cLen nonce c k m zbytes gv :=
  PROP ()
  LOCAL (lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z;
(*   temp _c c; temp _m m;*)
   (*temp _b (Vlong (Int64.sub bInit (Int64.repr r64)));*) temp _n nonce;
   temp _k k; gvars gv)
  SEP (data_at_ Tsh (Tarray tuchar 16 noattr) z;
      data_at_ Tsh (Tarray tuchar 64 noattr) x; Sigma_vector (gv _sigma);
      SByte Nonce nonce; ThirtyTwoByte K k; message_at mCont m;
      (if Int64.eq b Int64.zero 
       then data_at_ Tsh (Tarray tuchar cLen noattr) c
       else EX COUT:_, !!ContSpec b SIGMA K m mCont zbytes COUT && 
            data_at Tsh (Tarray tuchar cLen noattr) (Bl2VL COUT) c)).

Lemma crypto_stream_salsa20_xor_ok: semax_body SalsaVarSpecs SalsaFunSpecs
      f_crypto_stream_salsa20_tweet_xor
      crypto_stream_salsa20_xor_spec.
Proof. 
start_function.
rename H into MLEN.
(*assert_PROP (isptr v_z) as isptrZ by entailer!.*)

forward_if (b <> Int64.zero).
{ forward.
  change (Int64.unsigned _) with 0.
  unfold crypto_stream_xor_postsep. 
  rewrite Int64.eq_true. cancel.
 }
{ forward. entailer!!. }
Intros. rename H into B.
assert_PROP (field_compatible (Tarray tuchar (Int64.unsigned b) noattr) [] c) as FC by entailer!.
freeze FR1 := - (data_at_ _ _ v_z).
forward_for_simple_bound 16 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _x (tarray tuchar 64) v_x; lvar _z (tarray tuchar 16) v_z;
   temp _c c; temp _m m; temp _b (Vlong b); temp _n nonce; temp _k k; gvars gv)
   SEP  (FRZL FR1; EX l:_, !!(Zlength l + i = 16) && data_at Tsh (tarray tuchar 16) 
          ((Zrepeat (Vint Int.zero) i) ++ l) v_z))).
{Exists  (default_val (tarray tuchar 16)). simpl app. entailer!!. }
{ rename H into I. Intros l. rename H into LI16.
  forward. Exists (sublist 1 (Zlength l) l). entailer!!. list_solve. list_simplify.
}
Intros l. destruct l; [clear H | list_solve].
rewrite app_nil_r.
thaw FR1.
freeze FR2 := - (SByte Nonce _) (data_at _ _ _ v_z).
unfold SByte.
forward_for_simple_bound 8 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _x (Tarray tuchar 64 noattr) v_x;
   lvar _z (Tarray tuchar 16 noattr) v_z; temp _c c; temp _m m;
   temp _b (Vlong b); temp _n nonce; temp _k k; gvars gv)
   SEP 
   (FRZL FR2; data_at Tsh (Tarray tuchar 16 noattr)
        (sublist 0 i (SixteenByte2ValList Nonce) ++
         (Zrepeat (Vint Int.zero) (16-i))) v_z;
   data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList Nonce) nonce))).
{ entailer!!. }
{ rename H into I.
  assert (ZWS: Int.zwordsize = 32) by reflexivity.
  destruct (SixteenByte2ValList_bytes Nonce) as [NBytes [NBytesL NB]]; rewrite NB.
  assert (NBytesZL: Zlength NBytes = 16). apply Zlength_length; simpl; lia.
  destruct (Znth_mapVint (map Int.repr (map Byte.unsigned NBytes)) i) as [v V]. 
    repeat rewrite Zlength_map. rewrite NBytesZL. lia. 
  assert (v = Int.repr (Byte.unsigned (Znth i NBytes))). {
    rewrite Znth_map in V by list_solve. inv V. list_simplify. 
  }
  subst v.
  destruct (Byte.unsigned_range_2 (Znth i NBytes)) as [VBmin VBmax]. 
  specialize Byte_max_unsigned_Int_max_unsigned; intros ByteIntMaxUnsigned.
  simpl.
  forward. 
  change (@Znth val Vundef) with (@Znth val _); rewrite V.
  entailer!!.
  forward.
  rewrite NB.
  entailer!!. 
  list_simplify. subst i0. simpl.
  rewrite zero_ext8_byte; auto.
}
(* BUG:  deadvars  incorrectly deletes  temp _n at this point. *)
drop_LOCAL 0%nat. (*remove temp i*)

(*Verification of loop while (b >=64) ...*)
rename c into cInit. rename m into mInit. rename b into bInit. thaw FR2.
set (ZeroQuadByte := (Byte.zero, Byte.zero, Byte.zero, Byte.zero):QuadByte).
destruct Nonce as [[[N0 N1] N2] N3].
  assert (sublist 0 8 (SixteenByte2ValList (N0, N1, N2, N3)) ++
       Zrepeat (Vint Int.zero) (16 - 8)
     = (SixteenByte2ValList (((N0, N1), ZeroQuadByte), ZeroQuadByte))).
  { do 2 rewrite SixteenByte2ValList_char.
   assert (Zlength (QuadByte2ValList N0) = 4) 
      by (rewrite Zlength_correct, QuadByteValList_length; reflexivity).
   assert (Zlength (QuadByte2ValList N1) = 4) 
      by (rewrite Zlength_correct, QuadByteValList_length; reflexivity).
   assert (Zlength (QuadByte2ValList ZeroQuadByte) = 4) 
      by (rewrite Zlength_correct, QuadByteValList_length; reflexivity).
  rewrite app_assoc.
  rewrite sublist_app1 by list_solve.
  rewrite app_assoc.
  f_equal. list_solve.
 }
  rewrite H; clear H.
  assert (I64MAX: Int64.max_unsigned = ltac:(let x := eval compute in Int64.max_unsigned in exact x))
     by reflexivity.
  destruct (SixteenByte2ValList_bytes (N0, N1, ZeroQuadByte, ZeroQuadByte)) as [zbytes [Lzbytes ZBytes]].
  rewrite ZBytes.
forward_while (Inv cInit mInit bInit k nonce v_x v_z (N0, N1,N2,N3) K mCont zbytes gv).
{ (*precondition*)
  Exists O mInit zbytes (@nil byte).
  unfold Bl2VL, tarray.
  rewrite Tarray_0_emp_iff 
   by (pose proof (Int64.unsigned_range bInit); auto with field_compatible).
  entailer!. 
  2:cancel. (* why didn't the entailer! do this? *)
  split; [split|].
  + destruct mInit; simpl in *; try contradiction. subst i; auto.
           rewrite Ptrofs.add_zero; trivial. 
  + constructor.
  + simpl. rewrite Int64.sub_zero_l; auto.
}
{ entailer!!. }
{ remember (Z.of_nat rounds * 64)%Z as r64.
  destruct (zle (r64 + 64) (Int64.unsigned bInit)).
  2:{ exfalso. assert (X: 64 > Int64.unsigned bInit - r64) by lia. clear g.
           pose proof (Int64.unsigned_range_2 bInit).
           unfold Int64.sub in HRE. rewrite (Int64.unsigned_repr r64) in HRE by lia.
           rewrite Int64.unsigned_repr in HRE; lia.
  }
  destruct H as [R64old [M CONT]]. rename l into R64next.
   
  destruct (SixteenByte2ValList_exists zbytesR) as [d D].
  { apply CONTCONT in CONT. rewrite <- CONT.
    eapply Zlength_ZCont. rewrite Zlength_correct, Lzbytes. reflexivity. }

  forward_call (gv _sigma, k, v_z, v_x, (d, SIGMA, K)). 
  { unfold CoreInSEP, SByte, Sigma_vector, tarray.
    rewrite D; unfold Bl2VL. cancel. }
Intros snuff. rename H into Snuff.

destruct (QuadChunks2ValList_bytes (map littleendian_invert snuff)) as [sr_bytes [SRBL SNR]].
assert (SRL: Zlength sr_bytes = 64). {
  rewrite map_length, (Snuffle20_length _ _ Snuff) in SRBL.
  rewrite Zlength_correct, SRBL. reflexivity.
  apply prepare_data_length.
}
freeze [0;2;3] FR3.
remember (offset_val r64 cInit) as c.

assert(INT64SUB: Int64.sub bInit (Int64.repr (r64 + 64)) =
           Int64.sub (Int64.sub bInit (Int64.repr r64)) (Int64.repr 64)).
{ clear - R64next R64old HRE Heqr64 I64MAX.
  destruct (Int64.unsigned_range_2 bInit).
  unfold Int64.sub.
  repeat rewrite Int64.unsigned_repr; try lia. f_equal; lia.
} 

(* assert_PROP (isptr c) as C by entailer!. *)
rewrite SNR.
forward_seq. 
apply (loop1 Espec (FRZL FR3) v_x v_z c mInit (Vlong (Int64.sub bInit (Int64.repr r64))) nonce k m sr_bytes mCont).
    eassumption.
    clear - SRL R64next R64old HRE Heqr64 MLEN; lia. lia.

(*continuation after the FOR(i,64) loop*)
Opaque prepare_data.
drop_LOCAL 0%nat.  (* delete temp _i *)
Intros xorlist. rename H into XOR.
rewrite sublist_same in XOR; try lia.
forward.
thaw FR3. unfold CoreInSEP. repeat flatten_sepcon_in_SEP.
freeze [1;2;3;4;5;6;7] FR4.
unfold SByte. 
forward_seq. rewrite D.
  apply (For_i_8_16_loop Espec (FRZL FR4) v_x v_z c m 
           (Vlong (Int64.sub bInit (Int64.repr r64))) nonce k zbytesR gv).
freeze [0;1] FR5.
forward.
forward.
rewrite Heqc. simpl.

forward_if (EX m:_,
  (PROP  (null_or_offset mInit (r64+64) m)
   LOCAL 
   (temp _c
      (force_val
         (sem_add_ptr_int tuchar Signed (offset_val r64 cInit)
            (Vint (Int.repr 64))));
   temp _b
     (Vlong
        (Int64.sub (Int64.sub bInit (Int64.repr r64))
           (Int64.repr (Int.signed (Int.repr 64)))));
   lvar _x (Tarray tuchar 64 noattr) v_x; lvar _z (Tarray tuchar 16 noattr) v_z;
   temp _m m; temp _n nonce; temp _k k; gvars gv)  SEP  (FRZL FR5))).
{  clear H v. apply denote_tc_test_eq_split; auto with valid_pointer.
   destruct mInit; simpl in M; try contradiction.
   destruct M as [II M]; rewrite M in *; auto with valid_pointer.
   rewrite M in *.
     thaw FR5; thaw FR4.
  assert (message_at mCont (Vptr b i)
      |-- valid_pointer
            (Vptr b (Ptrofs.add i (Ptrofs.repr (Z.of_nat rounds * 64))))). {
        unfold message_at. eapply derives_trans. apply data_at_memory_block.
        eapply derives_trans. apply memory_block_valid_pointer. simpl.
        3: apply derives_refl'. 3: reflexivity. rep_lia.
        apply top_share_nonidentity.
   }
  auto 50 with valid_pointer.
}
{ forward.
  Exists (force_val (sem_add_ptr_int tuchar Signed m (Vint (Int.repr 64)))).
  entailer!!.
  destruct mInit; simpl in M; try contradiction.
  destruct M as [II M]; rewrite M in *. contradiction. 
  rewrite M in *.  simpl. rewrite Ptrofs.add_assoc, ptrofs_add_repr. trivial. }
{ forward. Exists m. entailer!!. destruct mInit; simpl in M; try contradiction.
  simpl. apply M. inv M. }
intros.
thaw FR5. thaw FR4.
Intros x.
destruct cInit; try solve [destruct FC as [? _]; contradiction].
Exists (S rounds, x, snd (ZZ (ZCont rounds zbytes) 8), srbytes ++ xorlist).
unfold fst, snd.
rewrite  Nat2Z.inj_succ, <- Zmult_succ_l_reverse.
assert_PROP (field_compatible0
     (Tarray tuchar (Int64.unsigned bInit - r64) noattr) 
      (SUB 64) (Vptr b (Ptrofs.add i (Ptrofs.repr r64))))
   as FC2 by (entailer!; auto with field_compatible).
entailer!!.
rewrite INT64SUB.
split; auto.
specialize (CONTCONT _ _ _ _ _ _ _ _ CONT); intros; subst zbytesR.
 assert (Hx := CONT_succ SIGMA K mInit mCont zbytes rounds _ _ CONT _ D
    _ _ _ Snuff SNR XOR).
 unfold snd in Hx; exact Hx. (* why is this necessary? *)
 rewrite (CONTCONT _ _ _ _ _ _ _ _ CONT). 
  unfold SByte, Sigma_vector.
  cancel.

  assert (Zlength xorlist = 64). {
     unfold bxorlist in XOR; destruct (combinelist_Zlength _ _ _ _ _ XOR).
     rewrite H0. unfold bytes_at. 
    destruct mInit; list_solve.
  }
  assert (Zlength (Bl2VL xorlist) = 64) by (rewrite Zlength_Bl2VL; lia).
  remember (Z.of_nat rounds * 64)%Z as r64.
  apply CONT_Zlength in CONT.

  assert (field_compatible (Tarray tuchar (Z.of_nat rounds * 64 + 64) noattr) [] (Vptr b i)).
  { eapply field_compatible_array_smaller0. apply FC. lia. }

  erewrite (split2_data_at_Tarray_tuchar _ (Int64.unsigned bInit - r64) (Zlength (Bl2VL xorlist)))
    by list_solve.
  autorewrite with sublist. rewrite H1.
  rewrite field_address0_clarify by (unfold field_address0; simpl; rewrite if_true; simpl; trivial).
  simpl.
  assert (II:Int64.unsigned bInit - (Z.of_nat rounds * 64 + 64) = Int64.unsigned bInit - (Z.of_nat rounds * 64) - 64) by  lia.
  rewrite Heqr64.
  rewrite II, Ptrofs.add_assoc, ptrofs_add_repr. cancel.

  unfold Bl2VL. repeat rewrite map_app.
  erewrite (split2_data_at_Tarray_tuchar Tsh (Z.of_nat rounds * 64 + 64) (Z.of_nat rounds * 64))
      by list_solve.
  rewrite sublist_app1       by list_solve.
  rewrite sublist_same by list_solve.
  replace (Z.of_nat rounds * 64 + 64 - Z.of_nat rounds * 64) with 64 by lia.
  rewrite sublist_app2       by list_solve.
  rewrite sublist_same by list_solve.
  rewrite field_address0_clarify; simpl. rewrite Zplus_0_l, Z.mul_1_l; trivial.
  unfold field_address0; simpl. rewrite if_true; simpl; trivial.
  auto with field_compatible.
}

(*continuation if (b) {...} *)
remember (Z.of_nat rounds * 64)%Z as r64.
 assert (R64b: r64+64 > Int64.unsigned bInit).
           destruct (Int64.unsigned_range_2 bInit) as [X1 X2].
           unfold Int64.sub in HRE. rewrite (Int64.unsigned_repr r64) in HRE by lia.
           rewrite Int64.unsigned_repr in HRE; lia.
destruct H as [R64a [M CONT]]. 
  assert (RR: Int64.unsigned (Int64.sub bInit (Int64.repr r64)) = Int64.unsigned bInit - r64).
  { destruct (Int64.unsigned_range_2 bInit).
    unfold Int64.sub.
    repeat rewrite Int64.unsigned_repr; try lia. }
forward_if (IfPost v_z v_x bInit (N0, N1, N2, N3) K mCont (Int64.unsigned bInit) nonce cInit k mInit zbytes gv).
{ rename H into BR.
  destruct (SixteenByte2ValList_exists zbytesR) as [d D].
  { apply CONTCONT in CONT. rewrite <- CONT.
    eapply Zlength_ZCont. rewrite Zlength_correct, Lzbytes. reflexivity. }
  forward_call (gv _sigma, k, v_z, v_x, (d, SIGMA, K)). 
  { unfold CoreInSEP, SByte, Sigma_vector, tarray.
    unfold Bl2VL; rewrite D. cancel. }
  Intros snuff. rename H into Snuff.
  destruct (QuadChunks2ValList_bytes (map littleendian_invert snuff)) as [sr_bytes [SRBL SNR]].
  assert (Zlength sr_bytes = 64).
    rewrite map_length, (Snuffle20_length _ _ Snuff) in SRBL.
    rewrite Zlength_correct, SRBL. reflexivity.
    apply prepare_data_length.
  rename H into SRL.
  freeze [0;2;3] FR1.
  remember (offset_val r64 cInit) as c.
  assert (BB: Int64.unsigned (Int64.sub bInit (Int64.repr r64)) < Int.max_unsigned).
     rep_lia. 
  rewrite SNR, <- RR.
  eapply semax_post_flipped'.
  eapply (loop2 Espec (FRZL FR1) v_x v_z c mInit); try eassumption; try lia.
  unfold IfPost.
  Intros l.
  unfold typed_true in BR. inversion BR; clear BR.
  entailer!!.
   rename H1 into H8.
  rewrite RR in *. eapply negb_true_iff in H8. 
  unfold Int64.eq in H8. rewrite RR in H8. unfold Int64.zero in H8.
  rewrite Int64.unsigned_repr in H8. 2: lia.
  if_tac in H8. inv H8. clear H8. thaw FR1.
  unfold CoreInSEP.
  rewrite Int64.eq_false. 2: assumption.
  Exists (srbytes ++ l). unfold SByte.
  specialize (CONT_Zlength _ _ _ _ _ _ _ _ CONT); intros CZ.
  entailer!. 
  + red.
    assert (R: rounds = Z.to_nat (Int64.unsigned bInit / 64)).
    { remember (Int64.unsigned bInit) as p.
      erewrite <- Z.div_unique with (q:= Z.of_nat rounds).
       rewrite Nat2Z.id. trivial.
      instantiate (1:= p- 64 * Z.of_nat rounds). 2: lia.
      left. lia. } 
    rewrite <- R.
    assert (Arith1: (Int64.unsigned bInit / 64 * 64 = Z.of_nat rounds * 64)%Z).
        rewrite R; rewrite Z2Nat.id; trivial. 
        apply Z_div_pos; lia.
    assert (Arith2: Int64.unsigned bInit mod 64 = Int64.unsigned bInit - Z.of_nat rounds * 64).
    { symmetry; eapply Zmod_unique. lia. instantiate (1:=Z.of_nat rounds); lia. }
    rewrite Arith1, Arith2, (CONTCONT _ _ _ _ _ _ _ _ CONT).
    rewrite if_false.
    - exists zbytesR, srbytes, d, snuff, sr_bytes, l. 
      intuition.
    - trivial.
  + erewrite (split2_data_at_Tarray_tuchar _ (Int64.unsigned bInit) (Z.of_nat rounds * 64)).
    2: lia. 
    2: rewrite Zlength_Bl2VL in *; rewrite Zlength_app. 2: lia. 
    rewrite Zlength_Bl2VL in *; unfold Bl2VL in *.
    repeat rewrite map_app. autorewrite with sublist.
    unfold Sigma_vector. cancel. 
    rewrite field_address0_clarify; simpl.
    rewrite (*Heqc, *)Zplus_0_l, Z.mul_1_l; trivial.
    unfold field_address0; simpl.
    rewrite Zplus_0_l, Z.mul_1_l, if_true; trivial. 
    apply field_compatible_isptr in H13. 
    destruct cInit; simpl in *; try contradiction; trivial.
    auto with field_compatible.
}
{ forward.
  hnf in H. inversion H; clear H. rewrite RR in *. eapply negb_false_iff in H1. 
  unfold Int64.eq in H1. rewrite RR in H1. unfold Int64.zero in H1.
  rewrite Int64.unsigned_repr in H1 by lia.
  if_tac in H1. 2: inv H1. clear H1. 
  assert (XX: Int64.unsigned bInit = r64) by lia.
  rewrite XX in *. clear H RR.
  unfold IfPost, CoreInSEP.
  entailer!.
  rewrite Zminus_diag in *; rewrite Tarray_0_emp_iff_; try assumption.
  rewrite Int64.eq_false. 2: assumption.
  unfold (*liftx, lift, *) SByte. simpl. cancel.
  Exists srbytes. apply andp_right; trivial.
  apply prop_right. red. rewrite XX, Heqr64. 
  rewrite if_true. 
  + exists zbytesR. rewrite Z_div_mult_full, Nat2Z.id. assumption. lia.
  + symmetry. eapply Zdiv.Zmod_unique. lia.
    rewrite Z.mul_comm, Zplus_0_r. reflexivity.
}
unfold IfPost. 
forward.
unfold tarray; entailer!!.
unfold crypto_stream_xor_postsep. cancel.
destruct (Int64.eq bInit Int64.zero). trivial.
Intros l. Exists l. apply andp_right; trivial.
apply prop_right. exists zbytes. split; assumption.
all: fail.  (* make sure we're really done *)
Admitted.  (* Qed blows up *)
