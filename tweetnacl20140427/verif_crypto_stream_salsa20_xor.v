Require Import VST.floyd.proofauto.
Local Open Scope logic.
Require Import Coq.Lists.List. Import ListNotations.
Require Import sha.general_lemmas.

Require Import tweetnacl20140427.split_array_lemmas.
Require Import ZArith. 
Require Import tweetnacl20140427.tweetNaclBase.
Require Import tweetnacl20140427.Salsa20.
Require Import tweetnacl20140427.verif_salsa_base.
Require Import tweetnacl20140427.tweetnaclVerifiableC.
Require Import tweetnacl20140427.Snuffle. 
Require Import tweetnacl20140427.spec_salsa. Opaque Snuffle.Snuffle.

Lemma int_max_unsigned_int64_max_unsigned: Int.max_unsigned < Int64.max_unsigned.
Proof. cbv; trivial. Qed.

Lemma int_max_signed_int64_max_signed: Int.max_signed < Int64.max_signed.
Proof. cbv; trivial. Qed.

Lemma byte_unsigned_max_eq: Byte.max_unsigned = 255. reflexivity. Qed.

(*from verif_ld_st*)
Lemma Byte_unsigned_range_32 b: 0 <= Byte.unsigned b <= Int.max_unsigned.
Proof. destruct (Byte.unsigned_range_2 b). specialize Byte_Int_max_unsigned; omega. Qed.

Ltac canon_load_result ::= idtac.

Lemma Int64_sub_sub a b c: 
      Int64.min_signed <= - c <= Int64.max_signed ->
      Int64.min_signed <= - b <= Int64.max_signed ->
      Int64.sub a (Int64.repr (b + c)) =
      Int64.sub (Int64.sub a (Int64.repr b)) (Int64.repr c).
Proof. intros.
  rewrite Int64.sub_add_opp.
  rewrite Int64.sub_add_opp.
  rewrite Int64.sub_add_opp. rewrite Int64.add_assoc. f_equal.
  rewrite Int64.neg_repr.
  rewrite Int64.neg_repr.
  rewrite Int64.neg_repr.
  rewrite Int64.add_signed.
  rewrite Int64.signed_repr; trivial.
  rewrite Int64.signed_repr; trivial. f_equal. omega.
Qed.

Lemma sublist_hi_plus {A} (l:list A) lo a b: 0<=lo<=a -> 0<=b -> sublist lo (a + b) l =
   sublist lo a l ++ sublist a (a+b) l.
Proof. intros.
  unfold sublist.
  assert (X: a+b -lo = a-lo + b) by omega. rewrite X; clear X.
  rewrite Z2Nat.inj_add; try omega.
  assert (Y: a + b - a = b) by omega. rewrite Y; clear Y.
  rewrite <- Z2Nat.inj_add; try omega.
  rewrite <- Zfirstn_app; try omega. f_equal.
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
  rep_omega.
Qed.

Lemma Int_unsigned_repr_byte b: Int.unsigned (Int.repr (Byte.unsigned b)) = Byte.unsigned b.
Proof. rewrite Int.unsigned_repr. trivial. rep_omega.
Qed. 

Lemma zero_ext8_byte b: Int.zero_ext 8 (Int.repr (Byte.unsigned b)) = Int.repr (Byte.unsigned b).
Proof.
  apply zero_ext_inrange. 
  rewrite Int.unsigned_repr by rep_omega. simpl. rep_omega.
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
  + 
    rewrite (byte_testbit _ i) in H; trivial.
    rewrite (byte_testbit _ i) in H; trivial.
    inv H.
Qed.

Lemma Znth_sublist':
  forall (A : Type){d: Inhabitant A} (lo i hi : Z) (al : list A),
  0 <= lo ->
  Zlength al <= hi ->
  0 <= i <= hi - lo -> Znth i (sublist lo hi al) = Znth (i + lo) al.
Proof. intros. unfold Znth. destruct (zlt i 0). omega.
destruct (zlt (i + lo) 0). omega. unfold sublist.
destruct (zeq i (hi-lo)).
2:{ rewrite nth_firstn. 2: apply Z2Nat.inj_lt; try omega. rewrite nth_skipn, Z2Nat.inj_add; trivial. omega. }
rewrite <- e. rewrite nth_overflow. 2:{ rewrite firstn_length, skipn_length. apply Min.le_min_l. }
rewrite nth_overflow; trivial. subst i.
assert(hi - lo + lo= hi). omega. rewrite H2.
apply Z2Nat.inj_le in H0; try omega. rewrite ZtoNat_Zlength in H0. apply H0.
apply Zlength_nonneg.
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
Proof.
  unfold data_at. unfold field_at, data_at_rec, at_offset; simpl.
  unfold array_pred, unfold_reptype, aggregate_pred.array_pred. entailer.
Qed. 
Lemma Tarray_0_emp' sh c: field_compatible (Tarray tuchar 0 noattr) nil c ->
  emp |-- data_at sh (Tarray tuchar 0 noattr) nil c.
Proof. intros.
  unfold data_at. unfold field_at, data_at_rec, at_offset; simpl.
  unfold array_pred, unfold_reptype, aggregate_pred.array_pred. simpl.
  entailer.
Qed. 
Lemma Tarray_0_emp_iff sh c: field_compatible (Tarray tuchar 0 noattr) [] c ->
  data_at sh (Tarray tuchar 0 noattr) nil c = emp.
Proof. intros. apply pred_ext. apply Tarray_0_emp. apply Tarray_0_emp'; trivial.
Qed.

Lemma Tarray_0_emp_ sh c: data_at_ sh (Tarray tuchar 0 noattr) c |--  emp.
Proof.
  unfold data_at_. unfold field_at_, field_at, data_at_rec, at_offset; simpl.
  unfold array_pred, unfold_reptype, aggregate_pred.array_pred. entailer.
Qed. 
Lemma Tarray_0_emp'_ sh c: field_compatible (Tarray tuchar 0 noattr) nil c ->
  emp |-- data_at_ sh (Tarray tuchar 0 noattr) c.
Proof. intros.
  unfold data_at_, field_at_, field_at, data_at_rec, at_offset; simpl.
  unfold array_pred, unfold_reptype, aggregate_pred.array_pred. simpl.
  entailer.
Qed. 
Lemma Tarray_0_emp_iff_ sh c: field_compatible (Tarray tuchar 0 noattr) [] c ->
  data_at_ sh (Tarray tuchar 0 noattr) c = emp.
Proof. intros. apply pred_ext. apply Tarray_0_emp_. apply Tarray_0_emp'_; trivial.
Qed.

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

Lemma Int64_ltu_false x y: Int64.ltu x y = false ->
      0 <= Int64.unsigned y <= Int64.unsigned x.
Proof. 
  unfold Int64.ltu; intros. if_tac in H. discriminate.
  split. apply Int64.unsigned_range. omega.
Qed.

Lemma Zlength_Bl2VL l: Zlength (Bl2VL l) = Zlength l.
Proof. unfold Bl2VL. repeat rewrite Zlength_map. trivial.
Qed.

Lemma Bl2VL_app l m: Bl2VL (l ++ m) = Bl2VL l ++ Bl2VL m.
Proof. unfold Bl2VL. repeat rewrite map_app. trivial.
Qed.


Lemma ZZ_is_byte: forall n zbytes u U, ZZ zbytes n = (u,U) ->
   0<= Int.unsigned u <256.
Proof. induction n; simpl; intros.
+ inv H. unfold Int.one. 
  rewrite Int.unsigned_repr by rep_omega. rep_omega.
+ remember (ZZ zbytes n). destruct p. symmetry in Heqp. inv H. apply IHn in Heqp. clear IHn.
  destruct Heqp.
  remember (Znth (Z.of_nat n + 8) l) as b. clear Heqb.
  specialize Byte_max_unsigned_Int_max_unsigned; intros B.
  assert (B1: Byte.max_unsigned = 255) by reflexivity.
  assert (B2: two_p 8 = 256) by reflexivity. 
  destruct (Byte.unsigned_range_2 b). 
  rewrite Int.shru_div_two_p. rewrite (Int.unsigned_repr 8) by rep_omega.
  assert (B3: 0 <= Int.unsigned i + Byte.unsigned b <= Int.max_unsigned).
    split. omega. rep_omega. 
  assert (0 <= (Int.unsigned i + Byte.unsigned b) / two_p 8 < 256).
    split. apply Z_div_pos. cbv; trivial. omega.
    apply Zdiv_lt_upper_bound. cbv; trivial. omega. 
  rewrite Int.unsigned_repr; rewrite Int.unsigned_repr; trivial. omega.
Qed.


Definition i_8_16_inv F x z c b m nonce k zbytes gv: environ -> mpred := 
EX i:_,
  (PROP  ()
   LOCAL  (temp _u (Vint (fst (ZZ zbytes (Z.to_nat (i-8)))));
     lvar _x (Tarray tuchar 64 noattr) x;
     lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
     temp _b b; temp _n nonce; temp _k k; gvars gv)
   SEP  (F; data_at Tsh (Tarray tuchar 16 noattr) (Bl2VL (snd (ZZ zbytes (Z.to_nat (i-8))))) z)).

Definition for_loop_statement:=
Sfor (Sset _i (Econst_int (Int.repr 8) tint))
     (Ebinop Olt (Etempvar _i tuint) (Econst_int (Int.repr 16) tint) tint)
     (Ssequence
        (Ssequence
           (Sset _t'5
              (Ederef
                 (Ebinop Oadd (Evar _z (tarray tuchar 16))
                    (Etempvar _i tuint) (tptr tuchar)) tuchar))
           (Sset _u
              (Ebinop Oadd (Etempvar _u tuint)
                 (Ecast (Etempvar _t'5 tuchar) tuint) tuint)))
        (Ssequence
           (Sassign
              (Ederef
                 (Ebinop Oadd (Evar _z (tarray tuchar 16))
                    (Etempvar _i tuint) (tptr tuchar)) tuchar)
              (Etempvar _u tuint))
           (Sset _u
              (Ebinop Oshr (Etempvar _u tuint) (Econst_int (Int.repr 8) tint)
                 tuint))))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint) tuint)).

Lemma For_i_8_16_loop Espec F x z c m b nonce k zbytes gv:
@semax CompSpecs Espec 
  (func_tycontext f_crypto_stream_salsa20_tweet_xor SalsaVarSpecs SalsaFunSpecs nil)
  (PROP  ()
   LOCAL  (temp _u (Vint (Int.repr 1)); lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
   temp _b b; temp _n nonce;
   temp _k k; gvars gv)
   SEP  (F; data_at Tsh (Tarray tuchar 16 noattr) (Bl2VL zbytes) z))
 for_loop_statement
 (normal_ret_assert 
  ( PROP ()
    LOCAL (lvar _x (Tarray tuchar 64 noattr) x;
           lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
           temp _b b; temp _n nonce; temp _k k; gvars gv)
    SEP (F; data_at Tsh (Tarray tuchar 16 noattr) (Bl2VL (snd (ZZ zbytes 8))) z))).
Proof.
unfold for_loop_statement.
forward_for_simple_bound 16 (i_8_16_inv F x z c b m nonce k zbytes gv).
{ entailer!. }
{ rename H into I.
  remember (ZZ zbytes (Z.to_nat (i - 8))) as X. destruct X as [ui Zi]. 
  assert_PROP (Zlength (Bl2VL Zi) = 16) as L by entailer!.
  unfold Bl2VL in L; rewrite Zlength_map in L.
  destruct (Znth_mapVint (map Int.repr (map Byte.unsigned Zi)) i) as [vi Vi].
    omega.
  rewrite Znth_map in Vi.
  2: omega.
  inv Vi. unfold Bl2VL.
  forward.
  { entailer!.
    autorewrite with sublist in *.
    red. rewrite Int.unsigned_repr by rep_omega. rep_omega.
  } 
  simpl. rewrite Znth_map; [| omega].
    rewrite Zlength_map in L.
    rewrite Znth_map; try omega.
    rewrite Zlength_map in L.
    rewrite Znth_map; try omega. 
  forward.
  forward.
  assert (Q: Z.to_nat (i + 1 - 8) = S (Z.to_nat (i-8))).
    rewrite <- Z2Nat.inj_succ. f_equal. omega. omega.
  forward.
  assert_PROP (isptr z) as PtrZ by entailer!.
  entailer!. rewrite Q; simpl; rewrite <- HeqX; simpl.
  f_equal. assert (W:Z.of_nat (Z.to_nat (i - 8)) + 8 = i).
     rewrite Z2Nat.id; omega.
     rewrite W. f_equal.
     unfold Int.add. rewrite Int_unsigned_repr_byte. trivial.

  apply derives_refl'. f_equal.
  clear H2. unfold Bl2VL.
  rewrite Q; simpl; rewrite <- HeqX. 
  rewrite upd_Znth_map. f_equal. simpl.
  assert (W:Z.of_nat (Z.to_nat (i - 8)) + 8 = i). rewrite Z2Nat.id; omega.
  rewrite W. do 2 rewrite <- upd_Znth_map.
  rewrite Byte.unsigned_repr.
  + unfold Int.add. rewrite Int_unsigned_repr_byte.
    f_equal. unfold Int.zero_ext. f_equal. apply Int.equal_same_bits.
    intros j J. 
    rewrite Int.Zzero_ext_spec; trivial. rewrite (Byte.Ztestbit_mod_two_p 8); trivial.
    rewrite Int.unsigned_repr; trivial.
    symmetry in HeqX. apply ZZ_is_byte in HeqX.
    destruct (Byte.unsigned_range_2 (Znth i Zi)). rep_omega.
  + destruct (Z_mod_lt (Int.unsigned ui + Byte.unsigned (Znth i Zi)) 256). 
    omega. rewrite byte_unsigned_max_eq; omega.
}
Opaque ZZ.
entailer!.
Qed.

Definition null_or_offset x q y :=
match x with 
  Vint i => i=Int.zero /\ y=nullval
| Vptr _ _ => y=offset_val q x
| _ => False
end.

Definition byte_at x i mbytes :=
    match x with
     Vint _ => Byte.zero
   | _ => Znth i mbytes
    end.

Lemma bxorlist_snoc x q y b l mbytes xbytes
        (M:null_or_offset x q y )  
        (X: bxorlist (bytes_at x q (Zlength l) mbytes)
                     (sublist 0 (Zlength l) xbytes) = Some l):
        0<= q -> Zlength l < Zlength xbytes ->  q+ Zlength l < Zlength mbytes ->
        b = Byte.xor (byte_at x (Zlength l + q) mbytes)
                     (Znth (Zlength l) xbytes) -> 
  bxorlist (bytes_at x q (Zlength l  + 1) mbytes)
           (sublist 0 (Zlength l  + 1) xbytes) = Some (l ++ [b]).
Proof.
  specialize (Zlength_nonneg l). intros. unfold bytes_at. 
  rewrite (Z.add_assoc q), (sublist_hi_plus xbytes), (sublist_hi_plus mbytes). 
  destruct x; try contradiction.
      - destruct M as [M1 M2]. subst i y. simpl. simpl in X.
        rewrite Z2Nat.inj_add, <- list_repeat_app.
        apply bxorlist_app. assumption.
        rewrite sublist_len_1. simpl. subst b. reflexivity.
        omega. omega. omega.
      - simpl in M. subst y. (*rewrite M in *;*) simpl in X; simpl.
        rewrite sublist_len_1.
        apply bxorlist_app. assumption.
        rewrite sublist_len_1. subst b. rewrite Z.add_comm. reflexivity.
        omega. omega.
      - omega.
      - omega.
      - omega.
      - omega.
Qed.

Definition loop1_statement:=
Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tuint) (Econst_int (Int.repr 64) tint) tint)
     (Ssequence
        (Sifthenelse (Etempvar _m (tptr tuchar))
           (Ssequence
              (Sset _t'7
                 (Ederef
                    (Ebinop Oadd (Etempvar _m (tptr tuchar))
                       (Etempvar _i tuint) (tptr tuchar)) tuchar))
              (Sset _t'1 (Ecast (Etempvar _t'7 tuchar) tint)))
           (Sset _t'1 (Ecast (Econst_int (Int.repr 0) tint) tint)))
        (Ssequence
           (Sset _t'6
              (Ederef
                 (Ebinop Oadd (Evar _x (tarray tuchar 64))
                    (Etempvar _i tuint) (tptr tuchar)) tuchar))
           (Sassign
              (Ederef
                 (Ebinop Oadd (Etempvar _c (tptr tuchar)) (Etempvar _i tuint)
                    (tptr tuchar)) tuchar)
              (Ebinop Oxor (Etempvar _t'1 tint) (Etempvar _t'6 tuchar) tint))))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint) tuint)).

Lemma loop1 Espec F x z c mInit b nonce k m xbytes mbytes gv cLen 
      q (M: null_or_offset mInit q m)
      (Q: 0 <= q <= (Zlength mbytes) - 64) (CL: 64 <= cLen):
@semax CompSpecs Espec 
  (func_tycontext f_crypto_stream_salsa20_tweet_xor SalsaVarSpecs SalsaFunSpecs nil)
  (PROP  ()
   LOCAL  (lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
   temp _b b; temp _n nonce;
   temp _k k; gvars gv)
   SEP  (F;
   data_at Tsh (tarray tuchar 64)
     (map Vint (map Int.repr (map Byte.unsigned xbytes))) x;
   data_at_ Tsh (Tarray tuchar cLen noattr) c;
   message_at mbytes mInit))
loop1_statement
(normal_ret_assert 
  ( PROP  ()
    LOCAL  (temp _i (Vint (Int.repr 64)); lvar _x (Tarray tuchar 64 noattr) x;
       lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m; temp _b b;
       temp _n nonce; temp _k k; gvars gv)
    SEP  (F;
          data_at Tsh (tarray tuchar 64)
             (map Vint (map Int.repr (map Byte.unsigned xbytes))) x;
          message_at mbytes mInit;
         EX  l : list byte,
          !!(bxorlist (bytes_at mInit q 64 mbytes) (sublist 0 64 xbytes) = Some l) &&
          data_at Tsh (Tarray tuchar cLen noattr)
            (Bl2VL l ++ list_repeat (Z.to_nat (cLen - 64)) Vundef) c))).
Proof. intros.
Intros.
unfold loop1_statement.       
forward_for_simple_bound 64 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
   temp _b b; temp _n nonce;
   temp _k k; gvars gv)
   SEP (F;
     data_at Tsh (tarray tuchar 64)
       (map Vint (map Int.repr (map Byte.unsigned xbytes))) x;
     message_at mbytes mInit;
     EX l:_,!!(bxorlist (bytes_at mInit q i mbytes) 
                        (sublist 0 i xbytes)
               = Some l)
         && data_at Tsh (Tarray tuchar cLen noattr)
                        (Bl2VL l ++ list_repeat (Z.to_nat (cLen - i)) Vundef) c))).
{ entailer!. rewrite Zminus_0_r. autorewrite with sublist.
  Exists (@nil byte). 
  unfold Bl2VL; simpl.
  entailer!.
  destruct mInit; simpl in M; try contradiction.
  destruct M; subst; simpl; trivial.
  subst; simpl. autorewrite with sublist. trivial. }
rename H into I.
  Intros l. rename H into XOR.
  assert_PROP (isptr c) as C by entailer!.
  assert_PROP (Zlength xbytes = 64) as XL.
  { entailer!. repeat rewrite Zlength_map in H1. trivial. } 
  freeze [0;1;3] FR1.
  forward_if
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); lvar _x (Tarray tuchar 64 noattr) x;
      lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
      temp _b b; temp _n nonce; temp _k k; gvars gv;
      temp _t'1 (Vint (Int.repr (Byte.unsigned (byte_at mInit (i+q) mbytes)))))
   SEP  (FRZL FR1; message_at mbytes mInit)).
  { apply denote_tc_test_eq_split.
    + clear H XOR. destruct mInit; simpl in M; try contradiction.
      - destruct M. subst m. apply valid_pointer_null.
      - subst m. thaw FR1. apply sepcon_valid_pointer2.
        unfold message_at. 
        eapply derives_trans. apply data_at_memory_block.
        eapply derives_trans. apply memory_block_valid_pointer.
        3: apply derives_refl.
        simpl. rewrite Z.max_r. omega. apply Zlength_nonneg.
        apply top_share_nonidentity.
    + apply valid_pointer_null. }
  { unfold Bl2VL in *.
    destruct mInit; simpl in *; try contradiction.
    destruct M. { subst m; simpl in H; contradiction. } 
    clear H.
    unfold message_at. simpl in M. rewrite M in *. simpl in *.
    unfold tarray.
    assert_PROP (field_compatible (Tarray tuchar (Zlength mbytes) noattr) [] (Vptr b0 i0)) by entailer!.
    erewrite (split2_data_at_Tarray_tuchar _ _ q). 2: omega. 2: unfold Bl2VL; repeat rewrite Zlength_map; trivial. 
    normalize. unfold field_address0. simpl.
    destruct (field_compatible0_dec (Tarray tuchar (Zlength mbytes) noattr)
           [ArraySubsc q] (Vptr b0 i0)).
    2:{ elim n; clear n. apply field_compatible0_cons. simpl. split; trivial. omega. }
    assert (X: 0 + 1 * q = q) by omega. rewrite X; clear X. 
    forward; unfold Bl2VL; autorewrite with sublist. 
    + entailer!. 
        apply Byte.unsigned_range_2.
    + forward. erewrite (split2_data_at_Tarray_tuchar _ (Zlength mbytes) q).
      2: omega. 2: unfold Bl2VL; repeat rewrite Zlength_map; trivial. 
      unfold field_address0. entailer!.
      autorewrite with sublist. 
         if_tac; try contradiction.
      cancel.
  }
  { rewrite H in *; simpl in *. 
    destruct mInit; simpl in M; try contradiction.
    destruct M as [M _]. 2: discriminate.
    forward. entailer!.
  }  
  destruct (Znth_mapVint (map Int.repr (map Byte.unsigned xbytes)) i) as  [xi Xi].
    repeat rewrite Zlength_map. omega.
  thaw FR1. freeze [0;2;3] FR2.
  forward; change (@Znth val Vundef) with (@Znth val _); rewrite Xi.
  { entailer!.
   rewrite ?Znth_map in Xi by list_solve.
   inv Xi. 
   rewrite Int.unsigned_repr. apply Byte.unsigned_range_2. apply byte_unsigned_range_int_unsigned_max.
  } 
  thaw FR2. freeze [0;2;3] FR3.
  forward.
  { entailer!.
    clear H2.
    specialize (Zlength_combinelist _ _ _ _ XOR); intros LL.
    autorewrite with sublist in LL.
    rewrite upd_Znth_app2.  
    2:{ rewrite Zlength_Bl2VL. autorewrite with sublist. omega. }
    rewrite Zlength_Bl2VL, LL, Zminus_diag, upd_Znth0, sublist_list_repeat; try omega.
    2: autorewrite with sublist; omega.
    simpl. thaw FR3.
    rewrite Znth_map in Xi. inv Xi. 2: repeat rewrite Zlength_map; omega.
    rewrite Znth_map. 2: omega.
    remember (Byte.xor (byte_at mInit (Zlength l+q) mbytes) 
                       (Znth (Zlength l) xbytes)) as mybyte.
    Exists (l++ [mybyte]). cancel.
    apply andp_right.
    + apply prop_right. 
      eapply (bxorlist_snoc mInit q m mybyte l); trivial; omega.
    + autorewrite with sublist.
      apply derives_refl'. f_equal. unfold Bl2VL. subst mybyte. clear.
      repeat rewrite map_app. rewrite <- app_assoc. f_equal. simpl.
      f_equal.
      repeat rewrite zero_ext_inrange; try rewrite xor_byte_int; try rewrite Int.unsigned_repr; trivial;
        try apply Byte.unsigned_range_2;
        try apply byte_unsigned_range_3.
      assert (X:cLen - Zlength l - 1 = cLen - (Zlength l + 1)) by omega.
      rewrite X; trivial.
  }
apply andp_left2. apply derives_refl.
Qed.

Definition loop2Inv F x z c mInit m b nonce k gv q xbytes mbytes cLen: environ -> mpred:=
EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
   temp _b b; temp _n nonce;
   temp _k k; gvars gv)
   SEP (F;
     data_at Tsh (tarray tuchar 64)
       (map Vint (map Int.repr (map Byte.unsigned xbytes))) x;
     message_at mbytes mInit;
     EX l:_,!!(bxorlist (bytes_at mInit q i mbytes) 
                        (sublist 0 i xbytes)
               = Some l)
         && data_at Tsh (Tarray tuchar cLen noattr)
                        (Bl2VL l ++ list_repeat (Z.to_nat (cLen - i)) Vundef) c)).

Definition loop2_statement:=
Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tuint) (Etempvar _b tulong) tint)
     (Ssequence
        (Sifthenelse (Etempvar _m (tptr tuchar))
           (Ssequence
              (Sset _t'4
                 (Ederef
                    (Ebinop Oadd (Etempvar _m (tptr tuchar))
                       (Etempvar _i tuint) (tptr tuchar)) tuchar))
              (Sset _t'2 (Ecast (Etempvar _t'4 tuchar) tint)))
           (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tint)))
        (Ssequence
           (Sset _t'3
              (Ederef
                 (Ebinop Oadd (Evar _x (tarray tuchar 64))
                    (Etempvar _i tuint) (tptr tuchar)) tuchar))
           (Sassign
              (Ederef
                 (Ebinop Oadd (Etempvar _c (tptr tuchar)) (Etempvar _i tuint)
                    (tptr tuchar)) tuchar)
              (Ebinop Oxor (Etempvar _t'2 tint) (Etempvar _t'3 tuchar) tint))))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint) tuint)).

Lemma loop2 Espec F x z c mInit m b nonce k xbytes mbytes gv
      q (M: null_or_offset mInit q m) (Q: 0 <= q) (QB: q+Int64.unsigned b = Zlength mbytes) (*(CL: 64 > cLen) *) (*should be b <= cLen or so?*)
      (B: Int64.unsigned b < 64):
@semax CompSpecs Espec
  (func_tycontext f_crypto_stream_salsa20_tweet_xor SalsaVarSpecs SalsaFunSpecs nil)
  (PROP  ()
   LOCAL  (lvar _x (Tarray tuchar 64 noattr) x;
   lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
   temp _b (Vlong b); temp _n nonce;
   temp _k k; gvars gv)
   SEP  (F; data_at Tsh (tarray tuchar 64)
              (map Vint (map Int.repr (map Byte.unsigned xbytes))) x;
         data_at_ Tsh (Tarray tuchar (Int64.unsigned b) noattr) c;
         message_at mbytes mInit))

  loop2_statement

  (normal_ret_assert 
  ( PROP  ()
    LOCAL  ((*temp _i (Vlong b); *) lvar _x (Tarray tuchar 64 noattr) x;
       lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m; temp _b (Vlong b);
       temp _n nonce; temp _k k; gvars gv)
    SEP  (F;
          data_at Tsh (tarray tuchar 64)
             (map Vint (map Int.repr (map Byte.unsigned xbytes))) x;
          message_at mbytes mInit;
         EX  l : list byte,
          !!(bxorlist (bytes_at mInit q (Int64.unsigned b) mbytes) (sublist 0 (Int64.unsigned b) xbytes) = Some l) &&
          data_at Tsh (Tarray tuchar (Int64.unsigned b) noattr) (Bl2VL l) c))).
Proof. intros.
destruct (Int64.unsigned_range_2 b) as [bLo bHi].
abbreviate_semax.
unfold loop2_statement.
forward_for_simple_bound (Int64.unsigned b)
  (loop2Inv F x z c mInit m (Vlong b) nonce k gv q xbytes mbytes (Int64.unsigned b)).
  + entailer!.
    autorewrite with sublist. Exists (@nil byte).
    unfold Bl2VL; simpl. entailer!.
    destruct mInit; simpl in M; try contradiction.
    destruct M; subst. simpl. trivial.
    simpl. autorewrite with sublist. reflexivity.
  + rename H into I.
    Intros l. rename H into XOR.
  assert_PROP (isptr c) as C by entailer!.
  assert_PROP (Zlength xbytes = 64) as XL.
  { entailer!. repeat rewrite Zlength_map in H0. trivial. }
 
  freeze [0;1;3] FR1.
  forward_if
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr i)); lvar _x (Tarray tuchar 64 noattr) x;
      lvar _z (Tarray tuchar 16 noattr) z; temp _c c; temp _m m;
      temp _b (Vlong b); temp _n nonce; temp _k k; gvars gv;
      temp _t'2 (Vint (Int.repr (Byte.unsigned (byte_at mInit (i+q) mbytes)))))
   SEP  (FRZL FR1; message_at mbytes mInit)).
  { apply denote_tc_test_eq_split.
    + clear H XOR. destruct mInit; simpl in M; try contradiction.
      - destruct M. subst m. apply valid_pointer_null.
      - subst m. thaw FR1. apply sepcon_valid_pointer2.
        unfold message_at. 
        eapply derives_trans. apply data_at_memory_block.
        eapply derives_trans. apply memory_block_valid_pointer.
        3: apply derives_refl.
        simpl. rewrite Z.max_r. omega. apply Zlength_nonneg.
        apply top_share_nonidentity.
    + apply valid_pointer_null. }
  { unfold Bl2VL in *.
    destruct mInit; try contradiction; simpl in M. 
    destruct M; subst. red in H; simpl in H; contradiction.
    clear H.
    unfold message_at. rewrite M in *. simpl in *.
    unfold tarray.
    assert_PROP (field_compatible (Tarray tuchar (Zlength mbytes) noattr) [] (Vptr b0 i0)) by entailer!.
    erewrite (split2_data_at_Tarray_tuchar _ _ q). 2: omega. 2: unfold Bl2VL; repeat rewrite Zlength_map; trivial. 
    normalize. unfold field_address0. simpl.
    destruct (field_compatible0_dec (Tarray tuchar (Zlength mbytes) noattr)
           [ArraySubsc q] (Vptr b0 i0)).
    2:{ elim n; clear n. apply field_compatible0_cons. simpl. split; trivial. omega. }
    assert (X: 0 + 1 * q = q) by omega. rewrite X; clear X.
    forward; unfold Bl2VL; autorewrite with sublist.
    { entailer!.
      apply Byte.unsigned_range_2.  }
    forward. entailer!.
    erewrite (split2_data_at_Tarray_tuchar _ (Zlength mbytes) q).
      2: omega. 2: unfold Bl2VL; repeat rewrite Zlength_map; trivial. 
      unfold field_address0. simpl. 
         if_tac; try contradiction.
      rewrite Z.mul_1_l. cancel.
  }
  { rewrite H in *; simpl in *. 
    destruct mInit; simpl in M; try contradiction.
    destruct M as [M _]. 2: discriminate.
    forward. entailer!.
  } 
(*  forward. drop_LOCAL 10%nat. (*variable 187*) *)
  destruct (Znth_mapVint (map Int.repr (map Byte.unsigned xbytes)) i) as  [xi Xi].
    repeat rewrite Zlength_map. omega.
(*  rewrite Znth_map with (d':=Int.zero) in Xi.
  rewrite Znth_map with (d':=Z0) in Xi. inv Xi.*)
  thaw FR1. freeze [0;2;3] FR2.
  forward (*; rewrite Xi*).
  { entailer!.
    do 2 rewrite Znth_map by list_solve. red.
    rewrite Int.unsigned_repr. apply Byte.unsigned_range_2. 
    apply Byte_unsigned_range_32.
  }
  change (@Znth val Vundef) with (@Znth val _).
  rewrite Xi. 
  thaw FR2. freeze [0;2;3] FR3.
  forward. 
  intros. entailer!.
  specialize (Zlength_combinelist _ _ _ _ XOR); intros LL.
    autorewrite with sublist in LL.
    rewrite upd_Znth_app2.  
    2:{ rewrite Zlength_Bl2VL. autorewrite with sublist. omega. }
    rewrite Zlength_Bl2VL, LL, Zminus_diag, upd_Znth0, sublist_list_repeat; try omega.
    2: autorewrite with sublist; omega.
    simpl. thaw FR3. 
    rewrite Znth_map in Xi by list_solve. inv Xi.
    rewrite Znth_map by list_solve.
    remember (Byte.xor (byte_at mInit (Zlength l+q) mbytes) 
                       (Znth (Zlength l) xbytes)) as mybyte.
    Exists (l++ [mybyte]). cancel.
    apply andp_right.
    - apply prop_right. 
      eapply (bxorlist_snoc mInit q m mybyte l); trivial; omega.
    - autorewrite with sublist.
      apply derives_refl'. f_equal. unfold Bl2VL. subst mybyte. clear.
      repeat rewrite map_app. rewrite <- app_assoc. f_equal. simpl.
      f_equal.
      repeat rewrite zero_ext_inrange; try rewrite xor_byte_int; try rewrite Int.unsigned_repr; trivial;
        try apply Byte.unsigned_range_2;
        try apply byte_unsigned_range_3.
      assert (X:Int64.unsigned b - Zlength l - 1 = Int64.unsigned b - (Zlength l + 1)) by omega.
      rewrite X; trivial.
+ entailer!.
Intros l; Exists l.
rewrite Zminus_diag, list_repeat_0, app_nil_r.
entailer!.
Qed.

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
assert_PROP (isptr v_z) by entailer!. rename H into isptrZ.


forward_if
  (PROP  (b <> Int64.zero)
   LOCAL  (lvar _x (tarray tuchar 64) v_x; lvar _z (tarray tuchar 16) v_z;
   temp _c c; temp _m m; temp _b (Vlong b); temp _n nonce; temp _k k; gvars gv)
   SEP  (data_at_ Tsh (tarray tuchar 16) v_z;
   data_at_ Tsh (tarray tuchar 64) v_x; SByte Nonce nonce;
   data_at_ Tsh (Tarray tuchar (Int64.unsigned b) noattr) c; ThirtyTwoByte K k;
   Sigma_vector (gv _sigma); message_at mCont m
   (*data_at Tsh (tarray tuchar (Zlength mCont)) (Bl2VL mCont) m*))).
{ unfold typed_true, strict_bool_val in H. simpl in H. 
  unfold eval_unop in H. simpl in H.
  specialize (Int64.eq_spec b Int64.zero). intros.
  destruct (Int64.eq b Int64.zero); [ | inv H].
  clear H.
  forward. entailer!.
  unfold crypto_stream_xor_postsep. 
  rewrite Int64.eq_true. cancel. }
{ unfold typed_false, strict_bool_val in H. simpl in H.
  unfold eval_unop in H. simpl in H.
  specialize (Int64.eq_spec b Int64.zero). intros.
  destruct (Int64.eq b Int64.zero); simpl in *. inv H.
  clear H.
  forward. Time entailer!. }
Intros. rename H into B.
assert_PROP (field_compatible (Tarray tuchar (Int64.unsigned b) noattr) [] c) as FC by entailer!.
freeze [1;2;3;4;5;6] FR1.
forward_for_simple_bound 16 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _x (tarray tuchar 64) v_x; lvar _z (tarray tuchar 16) v_z;
   temp _c c; temp _m m; temp _b (Vlong b); temp _n nonce; temp _k k; gvars gv)
   SEP  (FRZL FR1; EX l:_, !!(Zlength l + i = 16) && data_at Tsh (tarray tuchar 16) 
          ((list_repeat (Z.to_nat i) (Vint Int.zero)) ++ l) v_z))).
{ Exists (list_repeat 16 Vundef). entailer!. }
{ rename H into I. Intros l. rename H into LI16.
  forward. Exists (sublist 1 (Zlength l) l). entailer!.
    rewrite Zlength_sublist; omega.
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
thaw FR1.
freeze [0;2;3;4;5] FR2.
unfold SByte.
forward_for_simple_bound 8 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _x (Tarray tuchar 64 noattr) v_x;
   lvar _z (Tarray tuchar 16 noattr) v_z; temp _c c; temp _m m;
   temp _b (Vlong b); temp _n nonce; temp _k k; gvars gv)
   SEP 
   (FRZL FR2; data_at Tsh (Tarray tuchar 16 noattr)
        (sublist 0 i (SixteenByte2ValList Nonce) ++
         (list_repeat (Z.to_nat (16-i)) (Vint Int.zero))) v_z;
   data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList Nonce) nonce))).
{ entailer!. }
{ rename H into I.
  assert (ZWS: Int.zwordsize = 32) by reflexivity.
  destruct (SixteenByte2ValList_bytes Nonce) as [NBytes [NBytesL NB]]; rewrite NB.
  assert (NBytesZL: Zlength NBytes = 16). apply Zlength_length; simpl; omega.
  destruct (Znth_mapVint (map Int.repr (map Byte.unsigned NBytes)) i) as [v V]. 
    repeat rewrite Zlength_map. rewrite NBytesZL. omega. 
  assert (v = Int.repr (Byte.unsigned (Znth i NBytes))).
    rewrite Znth_map in V. inv V. 
    2: repeat rewrite Zlength_map; rewrite NBytesZL; simpl; omega.
    rewrite Znth_map.
    2: rewrite Zlength_map, NBytesZL; simpl; omega.
    rewrite Znth_map. reflexivity.
    rewrite NBytesZL; simpl; omega.
  subst v.
  destruct (Byte.unsigned_range_2 (Znth i NBytes)) as [VBmin VBmax]. 
  specialize Byte_max_unsigned_Int_max_unsigned; intros ByteIntMaxUnsigned.
  simpl.
  forward; change (@Znth val Vundef) with (@Znth val _); rewrite V.
  { entailer!. }
  forward.
  rewrite NB.
  entailer!.
  apply derives_refl'. f_equal.
  rewrite upd_Znth_app2; try autorewrite with sublist. 2: omega.
  rewrite upd_Znth0, <- (@sublist_rejoin val 0 i (i+1)), <- app_assoc. f_equal.
  rewrite <- Znth_cons_sublist.
  f_equal. rewrite Znth_map.
     rewrite Znth_map.
     rewrite Znth_map; trivial.
     omega. rewrite Zlength_map; omega. repeat rewrite Zlength_map; omega.
     autorewrite with sublist. rewrite  Z.sub_add_distr; trivial.
     autorewrite with sublist in *. omega.
     omega. 
     autorewrite with sublist in *. omega.
}
drop_LOCAL 0%nat. (*remove temp i*)

(*Verification of loop while (b >=64) ...*)
rename c into cInit. rename m into mInit. rename b into bInit. thaw FR2.


  remember ((Byte.zero, Byte.zero, Byte.zero, Byte.zero):QuadByte) as ZeroQuadByte.
  destruct Nonce as [[[N0 N1] N2] N3].
  assert (sublist 0 8 (SixteenByte2ValList (N0, N1, N2, N3)) ++
       list_repeat (Z.to_nat (16 - 8)) (Vint Int.zero)
     = (SixteenByte2ValList (((N0, N1), ZeroQuadByte), ZeroQuadByte))).
  { do 2 rewrite SixteenByte2ValList_char. 
    rewrite app_assoc, sublist_app1; try omega. 
        2: rewrite Zlength_app; do 2 rewrite Zlength_correct, QuadByteValList_length; simpl; omega.
    rewrite sublist_same; try omega. 
        2: rewrite Zlength_app; do 2 rewrite Zlength_correct, QuadByteValList_length; simpl; omega.
    subst ZeroQuadByte. simpl. rewrite Byte.unsigned_zero. rewrite <- app_assoc. reflexivity. }
  rewrite H; clear H.
  assert (Int64.max_unsigned = 18446744073709551615) by reflexivity. rename H into I64MAX.
  destruct (SixteenByte2ValList_bytes (N0, N1, ZeroQuadByte, ZeroQuadByte)) as [zbytes [Lzbytes ZBytes]].
  rewrite ZBytes.
forward_while (Inv cInit mInit bInit k nonce v_x v_z (N0, N1,N2,N3) K mCont zbytes gv).
{ (*precondition*)
  Exists O mInit. Exists zbytes (@nil byte).
  destruct (Int64.unsigned_range bInit). 
  specialize (Zlength_nonneg mCont); intros. unfold Bl2VL, tarray. 
  rewrite Int64.sub_zero_l, Zminus_0_r.
  rewrite Tarray_0_emp_iff; auto with field_compatible.
  normalize. entailer!. 
  split. + destruct mInit; simpl in *; try contradiction.
           subst i; split; trivial.
           rewrite Ptrofs.add_zero; trivial. 
         + constructor. 
}
{ entailer!. }
{ remember (Z.of_nat rounds * 64)%Z as r64.
  apply Int64_ltu_false in HRE; rewrite Int64.unsigned_repr in HRE. 2: omega.
  destruct (zle (r64 + 64) (Int64.unsigned bInit)).
  2:{ exfalso. assert (X: 64 > Int64.unsigned bInit - r64) by omega. clear g.
           destruct (Int64.unsigned_range_2 bInit) as [X1 X2].
           unfold Int64.sub in HRE. rewrite (Int64.unsigned_repr r64) in HRE. 2: omega.
           rewrite Int64.unsigned_repr in HRE; omega.
  }
  destruct H as [R64old [M CONT]]. rename l into R64next.
   
  destruct (SixteenByte2ValList_exists zbytesR) as [d D].
  { apply CONTCONT in CONT. rewrite <- CONT.
    eapply Zlength_ZCont. rewrite Zlength_correct, Lzbytes. reflexivity. }

  forward_call (gv _sigma, k, v_z, v_x, (d, SIGMA, K)). 
  { unfold CoreInSEP, SByte, Sigma_vector, tarray. cancel.
    rewrite D; unfold Bl2VL. cancel. }
Intros snuff. rename H into Snuff.

destruct (QuadChunks2ValList_bytes (map littleendian_invert snuff)) as [sr_bytes [SRBL SNR]].
assert (Zlength sr_bytes = 64).
  rewrite map_length, (Snuffle20_length _ _ Snuff) in SRBL.
  rewrite Zlength_correct, SRBL. reflexivity.
  apply prepare_data_length.
rename H into SRL.
freeze [0;2;3] FR3.
remember (offset_val r64 cInit) as c.

assert(INT64SUB: Int64.sub bInit (Int64.repr (r64 + 64)) =
           Int64.sub (Int64.sub bInit (Int64.repr r64)) (Int64.repr 64)).
{ clear - R64next R64old HRE Heqr64 I64MAX.
  destruct (Int64.unsigned_range_2 bInit).
  unfold Int64.sub.
  repeat rewrite Int64.unsigned_repr; try omega. f_equal; omega.
} 

assert_PROP (isptr c) as C by entailer!.
rewrite SNR.
forward_seq. (*
mkConciseDelta SalsaVarSpecs SalsaFunSpecs
      f_crypto_stream_salsa20_tweet_xor Delta.
eapply semax_extensionality_Delta.*)
  apply (loop1 Espec (FRZL FR3) v_x v_z c mInit (Vlong (Int64.sub bInit (Int64.repr r64))) nonce k m sr_bytes mCont).
    eassumption.
    clear - SRL R64next R64old HRE Heqr64 MLEN. rewrite MLEN. omega. omega.

(*continuation after the FOR(i,64) loop*)
Opaque prepare_data.
drop_LOCAL 0%nat.
Intros xorlist. rename H into XOR.
rewrite sublist_same in XOR; try omega.
forward.
thaw FR3. unfold CoreInSEP. repeat flatten_sepcon_in_SEP.
freeze [1;2;3;4;5;6;7;8] FR4.
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
{  clear H v. apply denote_tc_test_eq_split.
   destruct mInit; simpl in M; try contradiction.
   destruct M as [II M]; rewrite M in *.
     apply valid_pointer_null.
   rewrite M in *.
     thaw FR5; thaw FR4. apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
        apply sepcon_valid_pointer2.  apply sepcon_valid_pointer2.  apply sepcon_valid_pointer2.
         apply sepcon_valid_pointer2.  apply sepcon_valid_pointer1. entailer!.
        unfold message_at. eapply derives_trans. apply data_at_memory_block.
        eapply derives_trans. apply memory_block_valid_pointer. simpl.
        3: apply derives_refl'. 3: reflexivity.
        rewrite Z.max_r. omega. apply Zlength_nonneg.
        apply top_share_nonidentity.
     apply valid_pointer_null.
}
{ forward. Exists (force_val (sem_add_ptr_int tuchar Signed m (Vint (Int.repr 64)))). entailer!.
  destruct mInit; simpl in M; try contradiction.
  destruct M as [II M]; rewrite M in *. contradiction. 
  rewrite M in *.  simpl. rewrite Ptrofs.add_assoc, ptrofs_add_repr. trivial. }
{ forward. Exists m. entailer!. destruct mInit; simpl in M; try contradiction.
  simpl. apply M. inv M. }
intros.
thaw FR5. thaw FR4.
Intros x.
destruct cInit; simpl in Heqc; rewrite Heqc in C; try contradiction.
Exists (S rounds, x, snd (ZZ (ZCont rounds zbytes) 8), srbytes ++ xorlist).
unfold fst, snd.
rewrite  Nat2Z.inj_succ, <- Zmult_succ_l_reverse.
entailer!.
rewrite (*<- Heqr64,*) INT64SUB.
split; auto.
specialize (CONTCONT _ _ _ _ _ _ _ _ CONT); intros; subst zbytesR.
apply (CONT_succ SIGMA K mInit mCont zbytes rounds _ _ CONT _ D
    _ _ _ Snuff SNR XOR).
  unfold Int.min_signed, Int.max_signed; simpl.
  unfold SByte, Sigma_vector.
  cancel.
  rewrite (CONTCONT _ _ _ _ _ _ _ _ CONT). cancel.

  assert (Zlength xorlist = 64). {
     unfold bxorlist in XOR; destruct (combinelist_Zlength _ _ _ _ _ XOR).
     rewrite H15. unfold bytes_at. 
    destruct mInit; autorewrite with sublist; trivial.
  }
  assert (Zlength (Bl2VL xorlist) = 64) by (rewrite Zlength_Bl2VL; omega).
  remember (Z.of_nat rounds * 64)%Z as r64.
  apply CONT_Zlength in CONT.

  assert (field_compatible (Tarray tuchar (Z.of_nat rounds * 64 + 64) noattr) [] (Vptr b i)).
  { eapply field_compatible_array_smaller0. apply FC. omega. }

  erewrite (split2_data_at_Tarray_tuchar _ (Int64.unsigned bInit - r64) (Zlength (Bl2VL xorlist))).
  2: omega. 2: rewrite Zlength_app; autorewrite with sublist; omega.
  autorewrite with sublist. rewrite H16.
  rewrite field_address0_clarify; simpl.
  2:{ unfold field_address0; simpl. rewrite if_true; trivial.
           auto with field_compatible. }
  assert (II:Int64.unsigned bInit - (Z.of_nat rounds * 64 + 64) = Int64.unsigned bInit - (Z.of_nat rounds * 64) - 64). omega.
  rewrite Heqr64.
  rewrite II, Ptrofs.add_assoc, ptrofs_add_repr. entailer!.

  unfold Bl2VL. repeat rewrite map_app.
  erewrite (split2_data_at_Tarray_tuchar Tsh (Z.of_nat rounds * 64 + 64) (Z.of_nat rounds * 64)).
  2: omega.
  2: rewrite Zlength_app; repeat rewrite Zlength_map; omega.
  rewrite sublist_app1.
  2: omega.
  2: repeat rewrite Zlength_map; omega.
  rewrite sublist_same; trivial.
  2: repeat rewrite Zlength_map; omega.
  cancel.
  assert (XX: Z.of_nat rounds * 64 + 64 - Z.of_nat rounds * 64 = 64) by omega.
  rewrite XX, sublist_app2; repeat rewrite Zlength_map. 2: omega.
  rewrite sublist_same. 2: omega. 2: repeat rewrite Zlength_map; omega.
  repeat rewrite Zlength_map in *. rewrite CONT in *.
  apply derives_refl'. f_equal.
  rewrite field_address0_clarify; simpl. rewrite Zplus_0_l, Z.mul_1_l; trivial.
  unfold field_address0; simpl. rewrite if_true; trivial.
  auto with field_compatible.
}

(*continuation if (b) {...} *)
apply Int64.ltu_inv in HRE.
rewrite Int64.unsigned_repr in HRE. 2: omega.
remember (Z.of_nat rounds * 64)%Z as r64.
  destruct (zle (r64 + 64) (Int64.unsigned bInit)).
  exfalso. assert (X: 64 <= Int64.unsigned bInit - r64) by omega. clear l.
           destruct (Int64.unsigned_range_2 bInit) as [X1 X2].
           unfold Int64.sub in HRE. rewrite (Int64.unsigned_repr r64) in HRE. 2: omega.
           rewrite Int64.unsigned_repr in HRE; omega.
  destruct H as [R64a [M CONT]]. rename g into R64b. 
  assert (RR: Int64.unsigned (Int64.sub bInit (Int64.repr r64)) = Int64.unsigned bInit - r64).
  { destruct (Int64.unsigned_range_2 bInit).
    unfold Int64.sub.
    repeat rewrite Int64.unsigned_repr; try omega. }
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
  freeze [0;2;3;6] FR1.
  remember (offset_val r64 cInit) as c.
  assert (BB: Int64.unsigned (Int64.sub bInit (Int64.repr r64)) < Int.max_unsigned).
     rep_omega. 
(*mkConciseDelta SalsaVarSpecs SalsaFunSpecs
      f_crypto_stream_salsa20_tweet_xor Delta.*)
(*  eapply semax_extensionality_Delta.*)
  rewrite SNR, <- RR.
  eapply semax_post_flipped'.
  eapply (loop2 Espec (FRZL FR1) v_x v_z c mInit); try eassumption; try omega.
  unfold IfPost.
  entailer!.
  unfold typed_true in BR. inversion BR; clear BR.
   rename H3 into H8.
  rewrite RR in *. eapply negb_true_iff in H8. 
  unfold Int64.eq in H8. rewrite RR in H8. unfold Int64.zero in H8.
  rewrite Int64.unsigned_repr in H8. 2: omega.
  if_tac in H8. inv H8. clear H8. thaw FR1.
  unfold CoreInSEP.
  rewrite Int64.eq_false. 2: assumption.
  Intros l.
  Exists (srbytes ++ l). unfold SByte.
  specialize (CONT_Zlength _ _ _ _ _ _ _ _ CONT); intros CZ.
  entailer!. 
  + red.
    assert (R: rounds = Z.to_nat (Int64.unsigned bInit / 64)).
    { (*clear H17 Heqc H21 H20 H10 H2 M. clear H22 H23 H19 H18 H16 H15 H13 H12 H24 H25.
      clear H H0 H5 H6 H8 H7 ZBytes H11 H14. clear SNR SRBL D Snuff.
      clear RR. clear SRL CZ HRE BB POSTCONDITION MLEN Lzbytes CONT.*)
      remember (Int64.unsigned bInit) as p.
      erewrite <- Z.div_unique with (q:= Z.of_nat rounds).
       rewrite Nat2Z.id. trivial.
      instantiate (1:= p- 64 * Z.of_nat rounds). 2: omega.
      left. omega. } 
    rewrite <- R.
    assert (Arith1: (Int64.unsigned bInit / 64 * 64 = Z.of_nat rounds * 64)%Z).
        rewrite R; rewrite Z2Nat.id; trivial. 
        apply Z_div_pos; omega.
    assert (Arith2: Int64.unsigned bInit mod 64 = Int64.unsigned bInit - Z.of_nat rounds * 64).
        eapply Zmod_unique. instantiate (1:=Z.of_nat rounds); omega. omega. 
    rewrite Arith1, Arith2, (CONTCONT _ _ _ _ _ _ _ _ CONT).
    rewrite if_false.
    - exists zbytesR, srbytes, d, snuff, sr_bytes, l. 
      intuition.
    - trivial.
  + erewrite (split2_data_at_Tarray_tuchar _ (Int64.unsigned bInit) (Z.of_nat rounds * 64)).
    2: omega. 
    2: rewrite Zlength_Bl2VL in *; rewrite Zlength_app. 2: omega. 
    rewrite Zlength_Bl2VL in *; unfold Bl2VL in *.
    repeat rewrite map_app. autorewrite with sublist.
    cancel. unfold Sigma_vector. cancel. 
    rewrite field_address0_clarify; simpl.
    rewrite (*Heqc, *)Zplus_0_l, Z.mul_1_l; trivial.
    unfold field_address0; simpl.
    rewrite Zplus_0_l, Z.mul_1_l, if_true; trivial. 
    apply field_compatible_isptr in H16. 
    destruct cInit; simpl in *; try contradiction; trivial.
    auto with field_compatible.
}
{ forward.
  unfold typed_false in H. inversion H; clear H. rewrite RR in *. eapply negb_false_iff in H1. 
  unfold Int64.eq in H1. rewrite RR in H1. unfold Int64.zero in H1.
  rewrite Int64.unsigned_repr in H1. 2: omega.
  if_tac in H1. 2: inv H1. clear H1. 
  assert (XX: Int64.unsigned bInit = r64) by omega.
  rewrite XX in *. clear H RR.
  unfold IfPost, CoreInSEP.
  entailer!.
  rewrite Zminus_diag in *; rewrite Tarray_0_emp_iff_; try assumption.
  rewrite Int64.eq_false. 2: assumption.
  unfold (*liftx, lift, *) SByte. simpl. cancel.
  Exists srbytes. apply andp_right; trivial.
  apply prop_right. red. rewrite XX, Heqr64. 
  rewrite if_true. 
  + exists zbytesR. rewrite Z_div_mult_full, Nat2Z.id. assumption. omega.
  + symmetry. eapply Zdiv.Zmod_unique. omega.
    rewrite Z.mul_comm, Zplus_0_r. reflexivity.
}
unfold IfPost. 
forward.
unfold tarray; entailer!.
unfold crypto_stream_xor_postsep. cancel.
destruct (Int64.eq bInit Int64.zero). trivial.
Intros l. Exists l. apply andp_right; trivial.
apply prop_right. exists zbytes. split; assumption.
Time Qed. (*June 4th, 2017 (laptop):Finished transaction in 10.409 secs (8.611u,0.027s) (successful) *)