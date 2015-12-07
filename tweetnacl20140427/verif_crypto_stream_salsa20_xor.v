Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import general_lemmas.

Require Import split_array_lemmas.
Require Import ZArith. 
Require Import tweetNaclBase.
Require Import Salsa20.
Require Import verif_salsa_base.
Require Import tweetnaclVerifiableC.
Require Import Snuffle. 
Require Import spec_salsa. Opaque Snuffle.Snuffle.

Lemma sublist_hi_plus {A} (l:list A) lo a b: 0<=lo<=a -> 0<=b -> sublist lo (a + b) l =
   sublist lo a l ++ sublist a (a+b) l.
Proof. intros.
  unfold sublist.
  assert (X: a+b -lo = a-lo + b) by omega. rewrite X; clear X.
  rewrite Z2Nat.inj_add, <- firstn_app; try omega. f_equal.
  assert (Y: a + b - a = b) by omega. rewrite Y; clear Y.
  rewrite skipn_skipn, Z2Nat.inj_sub; try omega.
  f_equal. f_equal. rewrite <- le_plus_minus; trivial.
  apply Z2Nat.inj_le; omega.
Qed.

Lemma sublist0_hi_plus {A} (l:list A) a b: 0<=a -> 0<=b -> sublist 0 (a + b) l =
   sublist 0 a l ++ sublist a (a+b) l.
Proof. intros.
  apply sublist_hi_plus; omega.
Qed.

Lemma byte_unsigned_range_3 b: 0 <= Byte.unsigned b <= Int.max_unsigned.
Proof.
  destruct (Byte.unsigned_range_2 b). unfold Byte.max_unsigned in H0; simpl in H0.
  rewrite int_max_unsigned_eq; omega.
Qed.

Lemma Int_unsigned_repr_byte b: Int.unsigned (Int.repr (Byte.unsigned b)) = Byte.unsigned b.
Proof. rewrite Int.unsigned_repr. trivial.
  apply byte_unsigned_range_3 .
Qed. 

Lemma zero_ext8_byte b: Int.zero_ext 8 (Int.repr (Byte.unsigned b)) = Int.repr (Byte.unsigned b).
  apply zero_ext_inrange.
  rewrite Int.unsigned_repr. apply Byte.unsigned_range_2.
  apply byte_unsigned_range_3. 
Qed.

Lemma Zlxor_range_byte b1 b2: 0<= Z.lxor (Byte.unsigned b1) (Byte.unsigned b2) <= Byte.max_unsigned.
Proof.
  destruct (Byte.unsigned_range_2 b1).
  destruct (Byte.unsigned_range_2 b2).
  split. apply Z.lxor_nonneg. omega. 
  apply Byte.Ztestbit_le. omega. clear.
  intros i I H. rewrite Z.lxor_spec in H.
  destruct (zlt i 8).
  + clear - I l.  
    destruct (zeq i 0); subst. reflexivity.
    destruct (zeq i 1); subst. reflexivity.
    destruct (zeq i 2); subst. reflexivity.
    destruct (zeq i 3); subst. reflexivity.
    destruct (zeq i 4); subst. reflexivity.
    destruct (zeq i 5); subst. reflexivity.
    destruct (zeq i 6); subst. reflexivity.
    destruct (zeq i 7); subst. reflexivity. omega. 
  + rewrite (isbyteZ_testbit _ i) in H; trivial. 2: apply Byte.unsigned_range.
    rewrite (isbyteZ_testbit _ i) in H; trivial. 2: apply Byte.unsigned_range.
    inv H.
Qed.

Lemma xor_byte_int b1 b2: Int.xor (Int.repr (Byte.unsigned b1)) (Int.repr (Byte.unsigned b2)) =
      Int.repr (Byte.unsigned (Byte.xor b1 b2)).
Proof.
unfold Byte.xor, Int.xor.
  rewrite Byte.unsigned_repr. 
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr; trivial.
  apply byte_unsigned_range_3.
  apply byte_unsigned_range_3.
  apply Zlxor_range_byte.
Qed.

Lemma Zlength_combinelist {A} f xs ys l:
      combinelist A f xs ys = Some l -> Zlength l = Zlength ys.
Proof. intros H; symmetry in H.
  apply combinelist_length in H. rewrite Zlength_correct, H. rewrite Zlength_correct; reflexivity.
Qed. 

Lemma Tarray_0_emp sh v c: data_at sh (Tarray tuchar 0 noattr) v c |--  emp.
  unfold data_at. unfold field_at, data_at', at_offset; simpl.
  unfold array_pred, unfold_reptype, aggregate_pred.array_pred. entailer.
Qed. 
Lemma Tarray_0_emp' sh c: field_compatible (Tarray tuchar 0 noattr) nil c ->
  emp |-- data_at sh (Tarray tuchar 0 noattr) nil c.
Proof. intros.
  unfold data_at. unfold field_at, data_at', at_offset; simpl.
  unfold array_pred, unfold_reptype, aggregate_pred.array_pred. simpl.
  entailer.
Qed. 
Lemma Tarray_0_emp_iff sh c: field_compatible (Tarray tuchar 0 noattr) [] c ->
  data_at sh (Tarray tuchar 0 noattr) nil c = emp.
Proof. intros. apply pred_ext. apply Tarray_0_emp. apply Tarray_0_emp'; trivial.
Qed.

Lemma Tarray_0_emp_ sh c: data_at_ sh (Tarray tuchar 0 noattr) c |--  emp.
  unfold data_at_. unfold field_at_, field_at, data_at', at_offset; simpl.
  unfold array_pred, unfold_reptype, aggregate_pred.array_pred. entailer.
Qed. 
Lemma Tarray_0_emp'_ sh c: field_compatible (Tarray tuchar 0 noattr) nil c ->
  emp |-- data_at_ sh (Tarray tuchar 0 noattr) c.
Proof. intros.
  unfold data_at_, field_at_, field_at, data_at', at_offset; simpl.
  unfold array_pred, unfold_reptype, aggregate_pred.array_pred. simpl.
  entailer.
Qed. 
Lemma Tarray_0_emp_iff_ sh c: field_compatible (Tarray tuchar 0 noattr) [] c ->
  data_at_ sh (Tarray tuchar 0 noattr) c = emp.
Proof. intros. apply pred_ext. apply Tarray_0_emp_. apply Tarray_0_emp'_; trivial.
Qed.

Definition bxorlist := combinelist _ Byte.xor. 
Definition xorlist := combinelist _ Int.xor.

Lemma Int64_ltu_false x y: Int64.ltu x y = false ->
      0 <= Int64.unsigned y <= Int64.unsigned x.
Proof. 
  unfold Int64.ltu; intros. if_tac in H. discriminate.
  split. apply Int64.unsigned_range. omega.
Qed.

(*TODO: refine non-zero-case of this spec, relating COUT to mCont and K and Nonce*)
Definition crypto_stream_xor_postsep b Nonce K mLen mCont cLen nonce c k m :=
  (if Int64.eq b Int64.zero 
   then data_at_ Tsh (Tarray tuchar cLen noattr) c
   else (EX COUT:_, data_at Tsh (Tarray tuchar cLen noattr) COUT c))
  * SByte Nonce nonce * ThirtyTwoByte K k * data_at Tsh (tarray tuchar mLen) mCont m.

Parameter SIGMA: SixteenByte.
Definition Sigma_vector : val -> mpred :=
  data_at Tsh (tarray tuchar 16) (SixteenByte2ValList SIGMA).

Lemma bxorlist_app xs2 ys2: forall xs1 ys1 zs1 zs2,
      bxorlist xs1 ys1 = Some zs1 -> bxorlist xs2 ys2 = Some zs2 ->
      bxorlist (xs1 ++ xs2) (ys1 ++ ys2) = Some(zs1 ++ zs2).
Proof. 
  induction xs1; intros; destruct ys1; simpl in *; inv H.
  apply H0. 
  unfold bind in *. remember (bxorlist xs1 ys1) as d.
  symmetry in Heqd; destruct d; inv H2.
  rewrite (IHxs1 _ _ _ Heqd H0); reflexivity.
Qed.

Definition Bl2VL (l: list byte) := map Vint (map Int.repr (map Byte.unsigned l)).

Lemma Znth_sublist':
  forall (A : Type) (lo i hi : Z) (al : list A) (d : A),
  0 <= lo ->
  Zlength al <= hi ->
  0 <= i <= hi - lo -> Znth i (sublist lo hi al) d = Znth (i + lo) al d.
Proof. intros. unfold Znth. destruct (zlt i 0). omega.
destruct (zlt (i + lo) 0). omega. unfold sublist.
destruct (zeq i (hi-lo)).
Focus 2. rewrite nth_firstn. 2: apply Z2Nat.inj_lt; try omega. rewrite nth_skipn, Z2Nat.inj_add; trivial. omega.
rewrite <- e. rewrite nth_overflow. Focus 2. rewrite firstn_length, skipn_length. apply Min.le_min_l.
rewrite nth_overflow; trivial. subst i.
assert(hi - lo + lo= hi). omega. rewrite H2.
apply Z2Nat.inj_le in H0; try omega. rewrite ZtoNat_Zlength in H0. apply H0.
apply Zlength_nonneg.
Qed.

Lemma Zlength_Bl2VL l: Zlength (Bl2VL l) = Zlength l.
Proof. unfold Bl2VL. repeat rewrite Zlength_map. trivial.
Qed.

(*Precondition length mCont = Int64.unsigned b comes from textual spec in
  http://doc.libsodium.org/advanced/salsa20.html. 
  TODO: support the following part of the tetxual spec:
      m and c can point to the same address (in-place encryption/decryption). 
     If they don't, the regions should not overlap.*)
Definition crypto_stream_salsa20_xor_spec :=
  DECLARE _crypto_stream_salsa20_tweet_xor
   WITH c : val, k:val, m:val, nonce:val, b:int64,
        Nonce : SixteenByte, K: SixteenByte * SixteenByte,
        mCont: list byte, SV:val
   PRE [ _c OF tptr tuchar, _m OF tptr tuchar, _b OF tulong,
         _n OF tptr tuchar, _k OF tptr tuchar]
      PROP (Zlength mCont = Int64.unsigned b)
      LOCAL (temp _c c; temp _m m; temp _b (Vlong b);
             temp _n nonce; temp _k k; gvar _sigma SV)
      SEP ( SByte Nonce nonce;
            data_at_ Tsh (Tarray tuchar (Int64.unsigned b) noattr) c;
            ThirtyTwoByte K k;
            Sigma_vector SV;
            data_at Tsh (tarray tuchar (Zlength mCont)) (Bl2VL mCont) m)
  POST [ tint ] 
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr 0)))
       SEP (Sigma_vector SV; 
            crypto_stream_xor_postsep b Nonce K (Zlength mCont) (Bl2VL mCont) (Int64.unsigned b) nonce c k m). 
            
Definition joinMXC i (mCont xCont: list int) (cCont: list val):=
   bind (xorlist (firstn i mCont) (firstn i xCont)) (fun l => Some (map Vint l ++ skipn i cCont)).

Lemma crypto_stream_salsa20_xor_ok: semax_body SalsaVarSpecs SalsaFunSpecs
      f_crypto_stream_salsa20_tweet_xor
      crypto_stream_salsa20_xor_spec.
Proof. 
start_function.
name c' _c.
name m' _m.
name b' _b.
name n' _n.
name k' _k.
abbreviate_semax.
rename lvar0 into z.
rename lvar1 into x.
rename H into MLEN.
assert_PROP (isptr z) by entailer!. rename H into isptrZ.
forward_if
  (PROP  (b <> Int64.zero)
   LOCAL  (lvar _x (tarray tuchar 64) x; lvar _z (tarray tuchar 16) z;
   temp _c c; temp _m m; temp _b (Vlong b); temp _n nonce; temp _k k; gvar _sigma SV)
   SEP  (data_at_ Tsh (tarray tuchar 16) z;
   data_at_ Tsh (tarray tuchar 64) x; SByte Nonce nonce;
   data_at_ Tsh (Tarray tuchar (Int64.unsigned b) noattr) c; ThirtyTwoByte K k;
   Sigma_vector SV; data_at Tsh (tarray tuchar (Zlength mCont)) (Bl2VL mCont) m)).
{ unfold typed_true, strict_bool_val in H. simpl in H. 
  unfold eval_unop in H. simpl in H.
  specialize (Int64.eq_spec b Int64.zero). intros.
  destruct (Int64.eq b Int64.zero); simpl in *. 2: inv H.
  clear H. 
  forward. Exists x z. entailer!. 
  unfold crypto_stream_xor_postsep. 
  rewrite Int64.eq_true. cancel. }
{ unfold typed_false, strict_bool_val in H. simpl in H.
  unfold eval_unop in H. simpl in H.
  specialize (Int64.eq_spec b Int64.zero). intros.
  destruct (Int64.eq b Int64.zero); simpl in *. inv H.
  clear H.  
  forward. Time entailer!. }
Intros. rename H into B.
forward_for_simple_bound 16 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _x (tarray tuchar 64) x; lvar _z (tarray tuchar 16) z;
   temp _c c; temp _m m; temp _b (Vlong b); temp _n nonce; temp _k k; gvar _sigma SV)
   SEP  (EX l:_, !!(Zlength l + i = 16) && data_at Tsh (tarray tuchar 16) 
          ((list_repeat (Z.to_nat i) (Vint Int.zero)) ++ l) z;
          data_at_ Tsh (tarray tuchar 64) x; SByte Nonce nonce;
   data_at_ Tsh (Tarray tuchar (Int64.unsigned b) noattr) c;
   ThirtyTwoByte K k; Sigma_vector SV;
   data_at Tsh (tarray tuchar (Zlength mCont)) (Bl2VL mCont) m))).
{ Exists (list_repeat 16 Vundef). entailer!. }
{ rename H into I. Intros l. rename H into LI16.
  forward. Exists (sublist 1 (Zlength l) l). entailer!.
    rewrite Zlength_sublist; omega.
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible. 
  simpl. rewrite isptr_offset_val_zero; trivial.
  apply derives_refl'. f_equal. 
  rewrite Z2Nat.inj_add, <- list_repeat_app, <- app_assoc; try omega. 
  rewrite upd_Znth_app2.
  rewrite Zlength_list_repeat, Zminus_diag, upd_Znth0. reflexivity. omega.
  repeat rewrite Zlength_list_repeat; omega. 
}
Intros l. destruct l.
2: specialize (Zlength_nonneg l); intros;
         rewrite Zlength_cons', Z.add_comm, Z.add_assoc in H; omega.
clear H. rewrite app_nil_r.
unfold SByte at 1.
forward_for_simple_bound 8 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
   temp _b (Vlong b); temp _n nonce; temp _k k; gvar _sigma SV)
   SEP 
   (data_at Tsh (Tarray tuchar 16 noattr)
        (sublist 0 i (SixteenByte2ValList Nonce) ++
         (list_repeat (Z.to_nat (16-i)) (Vint Int.zero))) z;
   data_at_ Tsh (Tarray tuchar 64 noattr) x;
   data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList Nonce) nonce;
   data_at_ Tsh (Tarray tuchar (Int64.unsigned b) noattr) c; ThirtyTwoByte K k;
   Sigma_vector SV;
   data_at Tsh (Tarray tuchar (Zlength mCont) noattr) (Bl2VL mCont) m))).
{ entailer!. }
{ rename H into I.
  assert (ZWS: Int.zwordsize = 32) by reflexivity.
  destruct (SixteenByte2ValList_bytes Nonce) as [NBytes [NBytesL NB]]; rewrite NB.
  assert (NBytesZL: Zlength NBytes = 16). apply Zlength_length; simpl; omega.
  destruct (Znth_mapVint (map Int.repr (map Byte.unsigned NBytes)) i Vundef) as [v V]. 
    repeat rewrite Zlength_map. rewrite NBytesZL. omega. 
  assert (v = Int.repr (Byte.unsigned (Znth i NBytes Byte.zero))).
    rewrite Znth_map' with (d':=Int.zero) in V. inv V. 
    2: repeat rewrite Zlength_map; rewrite NBytesZL; simpl; omega.
    rewrite Znth_map' with (d':=Z0).
    2: rewrite Zlength_map, NBytesZL; simpl; omega.
    rewrite Znth_map' with (d':=Byte.zero). reflexivity.
    rewrite NBytesZL; simpl; omega.
  subst v.
  destruct (Byte.unsigned_range_2 (Znth i NBytes Byte.zero)) as [VBmin VBmax]. 
  specialize Byte_max_unsigned_Int_max_unsigned; intros ByteIntMaxUnsigned.
  simpl.
  forward; rewrite V.
  { entailer!.
    rewrite zero_ext_inrange. 
      rewrite Int.unsigned_repr; trivial; omega.
      rewrite Int.unsigned_repr; trivial; omega.
  }
  simpl; rewrite zero_ext_inrange. 
  2: rewrite Int.unsigned_repr; trivial; omega.
  forward.
  rewrite NB.
  entailer!.
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible. 
  simpl. rewrite isptr_offset_val_zero; trivial.
  apply derives_refl'. f_equal.
  rewrite upd_Znth_app2; try autorewrite with sublist. 2: omega.
  rewrite upd_Znth0, <- (@sublist_rejoin val 0 i (i+1)), <- app_assoc. f_equal.
  rewrite <- Znth_cons_sublist with (d:=Vundef).
  f_equal. rewrite Znth_map' with (d':=Int.zero).
     rewrite Znth_map' with (d':=Z0).
     rewrite Znth_map' with (d':=Byte.zero); trivial.
     omega. rewrite Zlength_map; omega. repeat rewrite Zlength_map; omega.
     autorewrite with sublist. rewrite  Z.sub_add_distr; trivial.
     autorewrite with sublist in *. omega.
     omega. 
     autorewrite with sublist in *. omega.
}
drop_LOCAL 0%nat. (*remove temp i*)
(*freeze [2] FULLNONCE.*)
(*
(*Verification of loop while (b >=64) ...*)
Parameter merge : list byte -> SixteenByte * SixteenByte -> list val.
(*Definition WHILE (r:nat) mC K cC :=
    firstn (r * 64)%nat cC = merge (firstn (r * 64)%nat mC) K.
  (*TODO: add that all asigned-to locations in c are bytes*)*)
Parameter WHILE : nat -> list byte -> SixteenByte * SixteenByte -> list val -> Prop.*)
          
rename c into cInit. rename m into mInit. rename b into bInit.
Parameter CCont: (* rounds:*) nat -> list val.
Axiom CCont0: CCont O = nil.
Parameter ZCont: (*zcont:*) SixteenByte ->  (* rounds:*) nat -> SixteenByte.
Axioms ZCont0: forall zcont, ZCont zcont O = zcont.
(*Parameter MCont: (*mCont :*) list byte -> (* rounds:*) nat -> list byte.
Axioms MCont0: forall mcont, MCont mcont O = mcont.*)

Definition Inv cInit mInit bInit k nonce x z Nonce K SV mcont zcont:=
(EX rounds:nat, 
 let r64 := (Z.of_nat rounds * 64)%Z in
 let c := offset_val (Int.repr r64) cInit in
 let m := offset_val (Int.repr r64) mInit in
 let b := Int64.sub bInit (Int64.repr r64) in
  (PROP  ((*WHILE rounds mCont K cCont /\ *)
          (*Z.of_nat rounds * 64 <= Zlength mcont /\*)
          (*length cCont = (rounds * 64)%nat*)
          (*Int64.ltu (Int64.repr (Z.of_nat rounds * 64)) bInit = true*)
          0 <= r64 <= Int64.unsigned bInit)
   LOCAL  (lvar _x (Tarray tuchar 64 noattr) x;
           lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
           temp _b (Vlong b); temp _n nonce; temp _k k; gvar _sigma SV)
   SEP 
   (data_at Tsh (Tarray tuchar 16 noattr)
        (*(firstn (Z.to_nat 8) (SixteenByte2ValList Nonce) ++
         list_repeat (Z.to_nat 8) (Vint Int.zero))*) 
        (SixteenByte2ValList  (ZCont zcont rounds)) z;
   data_at_ Tsh (Tarray tuchar 64 noattr) x; Sigma_vector SV;
   data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList Nonce) nonce;
   ThirtyTwoByte K k; 

   data_at Tsh (Tarray tuchar  (Z.of_nat rounds * 64) noattr) (CCont rounds) cInit;
   data_at_ Tsh (Tarray tuchar (Int64.unsigned bInit - Z.of_nat rounds * 64) noattr) c;

   data_at Tsh (Tarray tuchar (Zlength mcont - Z.of_nat rounds * 64) noattr)
               (sublist (Z.of_nat rounds * 64)%Z (Zlength mcont) (Bl2VL mcont)) m;
   data_at_ Tsh (Tarray tuchar (Z.of_nat rounds * 64) noattr) mInit))).

  remember ((Byte.zero, Byte.zero, Byte.zero, Byte.zero):QuadByte) as ZeroQuadByte.
  destruct Nonce as [[[N0 N1] N2] N3].
  assert (sublist 0 8 (SixteenByte2ValList (N0, N1, N2, N3)) ++
       list_repeat (Z.to_nat (16 - 8)) (Vint Int.zero)
     = (SixteenByte2ValList (((N0, N1), ZeroQuadByte), ZeroQuadByte))).
     unfold  SixteenByte2ValList; simpl. 
    rewrite app_assoc, sublist_app1; try omega. 
        2: rewrite Zlength_app; do 2 rewrite Zlength_correct, QuadByteValList_length; simpl; omega.
    rewrite sublist_same; try omega. 
        2: rewrite Zlength_app; do 2 rewrite Zlength_correct, QuadByteValList_length; simpl; omega.
    subst ZeroQuadByte. simpl. rewrite Byte.unsigned_zero. rewrite <- app_assoc. reflexivity.
  rewrite H; clear H.
  assert (Int64.max_unsigned = 18446744073709551615) by reflexivity. rename H into I64MAX.

forward_while (Inv cInit mInit bInit k nonce x z (N0, N1,N2,N3) K SV mCont 
            (N0, N1, ZeroQuadByte, ZeroQuadByte)).
{ (*precondition*)
  Exists O. rewrite ZCont0, (*MCont0,*) CCont0. 
  destruct (Int64.unsigned_range bInit). 
  specialize (Zlength_nonneg mCont); intros. unfold Bl2VL.
  entailer!.
  rewrite Int64.sub_zero_l; trivial.
  do 2 rewrite Zminus_0_r.
   autorewrite with sublist. cancel.
   rewrite Tarray_0_emp_iff_; auto with field_compatible.
   rewrite Tarray_0_emp_iff; auto with field_compatible.
   cancel.
}
{ entailer!. }
{ remember (Z.of_nat rounds * 64)%Z as r64.
  apply Int64_ltu_false in HRE; rewrite Int64.unsigned_repr in HRE. 2: omega.
  destruct (zle (r64 + 64) (Int64.unsigned bInit)).
  Focus 2. exfalso. assert (X: 64 > Int64.unsigned bInit - r64) by omega. clear g.
           destruct (Int64.unsigned_range_2 bInit) as [X1 X2].
           unfold Int64.sub in HRE. rewrite (Int64.unsigned_repr r64) in HRE. 2: omega.
           rewrite Int64.unsigned_repr in HRE; omega.
  rename H into R64old. rename l into R64next.
  forward_call (SV, k, z, x, 
                 (ZCont (((N0, N1), ZeroQuadByte), ZeroQuadByte) rounds, SIGMA, K)). 
  { unfold CoreInSEP, SByte, Sigma_vector, tarray. cancel. }
Intros snuff. rename H into Snuff.

destruct (QuadChunks2ValList_bytes (map littleendian_invert snuff)) as [sr_bytes [SRBL SNR]].
(*  rewrite map_length, (Snuffle20_length _ _ HSnuffleRes) in SRBL.
  2: apply prepare_data_length.
  rewrite <- R in *. *)
assert (Zlength sr_bytes = 64).
  rewrite map_length, (Snuffle20_length _ _ Snuff) in SRBL.
  rewrite Zlength_correct, SRBL. reflexivity.
  apply prepare_data_length.
rename H into SRL.
freeze [0;2;3;6] FR1.
remember (offset_val (Int.repr r64) cInit) as c.
remember (offset_val (Int.repr r64) mInit) as m.
forward_for_simple_bound 64 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
   temp _b (Vlong (Int64.sub bInit (Int64.repr r64))); temp _n nonce;
   temp _k k; gvar _sigma SV)
   SEP (FRZL FR1;
     data_at Tsh (tarray tuchar 64)
       (QuadChunks2ValList (map littleendian_invert snuff)) x;
     data_at Tsh (Tarray tuchar (Zlength mCont - r64) noattr)
       (sublist r64 (Zlength mCont) (Bl2VL mCont)) m;
     EX l:_,
         !!(bxorlist (sublist 0 i (sublist r64 (Zlength mCont) mCont))
                     (sublist 0 i sr_bytes)
            = Some l)
         && data_at Tsh (Tarray tuchar ((Int64.unsigned bInit) - r64) noattr)
                        (Bl2VL l ++ list_repeat (Z.to_nat ((Int64.unsigned bInit) - r64 - i)) Vundef) c))).
{ entailer!. rewrite Zminus_0_r. 
  Exists (@nil byte). (* (list_repeat (Z.to_nat ((Int64.unsigned bInit) - r64)) Vundef). *)
  (*rewrite Zlength_list_repeat. *)
  unfold Bl2VL; simpl.
  entailer!. }
{ rename H into I.
  Intros l. rename H into XOR.
  assert_PROP (isptr m) by entailer!.
  apply isptrD in H. destruct H as [? [? MR]]. rewrite MR in *.
  forward_if
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
   temp _b (Vlong (Int64.sub bInit (Int64.repr r64))); temp _n nonce;
   temp _k k; gvar _sigma SV;
   temp 187%positive (Vint (Int.repr (Byte.unsigned (Znth i (sublist r64 (Zlength mCont) mCont) Byte.zero)))))
(*   temp _loop2left (Vint (Int.repr (Byte.unsigned (Znth i (sublist r64 (Zlength mCont) mCont) Byte.zero)))))*)
   SEP  (FRZL FR1;
   data_at Tsh (tarray tuchar 64)
     (QuadChunks2ValList (map littleendian_invert snuff)) x;
   data_at Tsh (Tarray tuchar (Zlength mCont - r64) noattr)
     (sublist r64 (Zlength mCont) (Bl2VL mCont)) m;
   data_at Tsh (Tarray tuchar (Int64.unsigned bInit - r64) noattr)
     (Bl2VL l ++
      list_repeat (Z.to_nat (Int64.unsigned bInit - r64 - i)) Vundef) c)).
  { apply denote_tc_comparable_split.
    + apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply data_at_valid_ptr.
      apply top_share_nonidentity.
      simpl. rewrite Z.mul_1_l, Z.max_r; omega.
    + entailer!. }
  { unfold Bl2VL in *. rename H into M.
    forward.
    { entailer!.
      rewrite Znth_sublist; try omega.
      rewrite Znth_map with (d':=Int.zero); trivial.
      repeat rewrite Zlength_map; omega. }
    rewrite MR in *.
    entailer!. clear - H0 I R64next R64old MLEN.
    rewrite Znth_sublist in H0; try omega. rewrite Znth_map with (d':=Int.zero) in H0.
    2: repeat rewrite Zlength_map; omega.
    simpl in H0. rewrite <- H0; clear H0.
    f_equal. erewrite (Znth_map _ _ (i + r64)) with (d':=Z0).
    2: repeat rewrite Zlength_map; omega.
    rewrite Znth_sublist; try omega. 
    rewrite Znth_map with (d':=Byte.zero); trivial. omega.
  }
  { inv H. } (*THIS CASE IS TRIVIAL -- m can't be NULL!!*) 

  forward. drop_LOCAL 10%nat. (*variable 187*)
  rewrite SNR.
  rewrite map_length, (Snuffle20_length _ _ Snuff (prepare_data_length _ )) in SRBL.
  destruct (Znth_mapVint (map Int.repr (map Byte.unsigned sr_bytes)) i Vundef) as  [xi Xi].
    repeat rewrite Zlength_map. rewrite SRL; omega.
  forward; rewrite Xi.
  { entailer!.
    clear - Xi I SRL.
    rewrite Znth_map with (d':= Int.zero) in Xi. inv Xi.
    eapply zero_ext_range2; try reflexivity. cbv; intuition.
    repeat rewrite Zlength_map. rewrite SRL; omega. }
  simpl. 

(*QINXIANG: THIS FORWARD CAUSES MEMORY EXHAUSTION*)
(*  forward.*)

apply semax_seq_skip. 
eapply semax_seq'.

ensure_open_normal_ret_assert;
hoist_later_in_pre;
match goal with
| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign ?e ?e2) _ =>
  (* Super canonical field store *)
    let e1 := fresh "e" in
    let efs := fresh "efs" in
    let tts := fresh "tts" in
      construct_nested_efield e e1 efs tts;

    let lr := fresh "lr" in
      pose (compute_lr e1 efs) as lr;
      vm_compute in lr;

    let HLE := fresh "H" in
    let p := fresh "p" in evar (p: val);
      match goal with
      | lr := LLLL |- _ => do_compute_lvalue Delta P Q R e1 p HLE
      | lr := RRRR |- _ => do_compute_expr Delta P Q R e1 p HLE
      end;

    let HRE := fresh "H" in
    let v0 := fresh "v" in evar (v0: val);
      do_compute_expr Delta P Q R (Ecast e2 (typeof (nested_efield e1 efs tts))) v0 HRE;

    let H_Denote := fresh "H" in
    let gfs := fresh "gfs" in
      solve_efield_denote Delta P Q R efs gfs H_Denote;

    let sh := fresh "sh" in evar (sh: share);
    let t_root := fresh "t_root" in evar (t_root: type);
    let gfs0 := fresh "gfs" in evar (gfs0: list gfield);
    let v := fresh "v" in evar (v: reptype (nested_field_type t_root gfs0));
    let n := fresh "n" in
    let H := fresh "H" in
    sc_new_instantiate P Q R R Delta e1 gfs tts lr p sh t_root gfs0 v n (0%nat) H;

    try (unify v (default_val (nested_field_type t_root gfs0));
          lazy beta iota zeta delta - [list_repeat Z.to_nat] in v);

    let gfs1 := fresh "gfs" in
    let len := fresh "len" in
    pose ((length gfs - length gfs0)%nat) as len;
    simpl in len;
    match goal with
    | len := ?len' |- _ =>
      pose (firstn len' gfs) as gfs1
    end;

    clear len;
    unfold gfs in gfs0, gfs1;
    simpl firstn in gfs1;
    simpl skipn in gfs0;

    change gfs with (gfs1 ++ gfs0) in *;
    subst gfs;

    eapply (semax_SC_field_store Delta sh n p)
      with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
    subst p;
      [ reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | exact HLE 
      | exact HRE | exact H_Denote | solve [auto]
      | solve_store_rule_evaluation
      | subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n;
        pre_entailer;
        try quick_typecheck3
        clear HLE HRE H_Denote H;
        unfold tc_efield; try solve[entailer!]; 
        simpl app; simpl typeof
      | subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n;
        clear HLE HRE H_Denote H
]
end. (*
IT SEEMS, THIS TACTIC IS TO BLAME: 
solve_legal_nested_field_in_entailment.*)

apply compute_legal_nested_field_spec.
  match goal with
  | |- Forall ?F _ =>
      let F0 := fresh "F" in
      remember F as F0;
      simpl;
      subst F0
  end.
  repeat constructor.
apply prop_right. clear - I R64next. omega.
(*entailer!.
  try solve [entailer!].

        solve_legal_nested_field_in_entailment.
     ]
end.

store_tac.
*)
  forward. (*Skip*)
  entailer!.
  clear H10 TC TC1 TC2 TC3 TC4 TC5.
  specialize (Zlength_combinelist _ _ _ _ XOR); intros LL.
  autorewrite with sublist in LL.
  rewrite upd_Znth_app2. 
  Focus 2. rewrite Zlength_Bl2VL. autorewrite with sublist. omega.
  rewrite SNR, field_at_data_at, Zlength_Bl2VL, LL, Zminus_diag, upd_Znth0, sublist_list_repeat; try omega.
  2: autorewrite with sublist; omega.
  simpl.
  rewrite Znth_map with (d':=Int.zero) in Xi. inv Xi. 2: repeat rewrite Zlength_map; omega.
  rewrite Znth_map with (d':=Z0). 2: rewrite Zlength_map; omega.
  rewrite Znth_map with (d':=Byte.zero). 2: omega. 
  Exists (l ++ [Byte.xor (Znth (Zlength l)
                               (sublist (Z.of_nat rounds * 64) (Zlength mCont) mCont)
                               Byte.zero)
                         (Znth (Zlength l) sr_bytes Byte.zero)]).
  cancel.
  apply andp_right.
  + apply prop_right. remember (sublist (Z.of_nat rounds * 64) (Zlength mCont) mCont) as MM.
    rewrite (sublist0_hi_plus MM); try omega. rewrite (sublist0_hi_plus sr_bytes); try omega.
    apply bxorlist_app. assumption.   
    autorewrite with sublist.
    rewrite pure_lemmas.sublist_singleton with (d:=Byte.zero).
    rewrite pure_lemmas.sublist_singleton with (d:=Byte.zero). reflexivity.
    rewrite SRL; omega.
    subst MM; autorewrite with sublist; omega.
  + autorewrite with sublist.
    rewrite field_address_offset by auto with field_compatible.   
    rewrite offset_offset_val; simpl. rewrite Int.add_zero.
    apply derives_refl'. f_equal.
    unfold Bl2VL. repeat rewrite map_app. rewrite <- app_assoc. f_equal.
    repeat rewrite map_app. simpl. f_equal.
    Focus 2. assert (X: Int64.unsigned bInit - Z.of_nat rounds * 64 - (Zlength l + 1) = Int64.unsigned bInit - Z.of_nat rounds * 64 - Zlength l - 1) by omega.
             rewrite X; trivial.
    f_equal.

  rewrite zero_ext8_byte.
  rewrite zero_ext8_byte.
  rewrite zero_ext_inrange.
  apply xor_byte_int.
  rewrite xor_byte_int. rewrite Int.unsigned_repr. apply Byte.unsigned_range_2.
  apply byte_unsigned_range_3.
 }  

(*continuation after the FOR(i,64) loop*)
drop_LOCAL 0%nat.
Intros xorlist. rename H into XOR.
forward.
thaw FR1. unfold CoreInSEP. repeat flatten_sepcon_in_SEP.
freeze [1;2;3;4;5;6;7;8] FR2.
unfold SByte.
apply -> seq_assoc; abbreviate_semax.
forward.

Parameter zVal:Z-> list val.

Definition forPOST FR2 bInit x z c r64 m nonce k SV: environ -> mpred :=
  (PROP  ()
   LOCAL  ((*temp _i (Vint (Int.repr (i+8))); temp _u (Vint (uVal i));*)
   lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
   temp _b (Vlong (Int64.sub bInit (Int64.repr r64))); temp _n nonce;
   temp _k k; gvar _sigma SV)
   SEP  (FRZL FR2;
   data_at Tsh (Tarray tuchar 16 noattr)
     (zVal 8) z)).

Parameter uVal:Z->int.

Definition forPRE FR2 bInit x z c r64 m nonce k SV i: environ -> mpred := 
  (PROP  (0<=i<=8)
   LOCAL  (temp _i (Vint (Int.repr ((i-1)+8))); temp _u (Vint (uVal i));
   lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
   temp _b (Vlong (Int64.sub bInit (Int64.repr r64))); temp _n nonce;
   temp _k k; gvar _sigma SV)
   SEP  (FRZL FR2;
   data_at Tsh (Tarray tuchar 16 noattr)
     (zVal i) z)).
Definition forINV FR2 bInit x z c r64 m nonce k SV: environ -> mpred := 
EX i:_,
  (PROP  (0<=i<=8)
   LOCAL  (temp _i (Vint (Int.repr (i+8))); temp _u (Vint (uVal i));
   lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
   temp _b (Vlong (Int64.sub bInit (Int64.repr r64))); temp _n nonce;
   temp _k k; gvar _sigma SV)
   SEP  (FRZL FR2;
   data_at Tsh (Tarray tuchar 16 noattr)
     (zVal i) z)).

apply semax_pre with (P':= forINV FR2 bInit x z c r64 m nonce k SV). 
{ Exists 0.  (*clear. drop_LOCAL 0%nat. *)(*QINXIANG: CALLING ENTAILER INSTEAD OF ENTAILER! CAUSES MEMORY EXHAUSTION HERE*)
  entailer!.
  admit.
  admit. (*zVal 0 = SixteenByte2ValList (ZCont (N0, N1, ZeroQuadByte, ZeroQuadByte) rounds)*)
}
admit.

} 

(*continuation if (b) {...} *)
admit.
Time Qed. (*121 secs*)