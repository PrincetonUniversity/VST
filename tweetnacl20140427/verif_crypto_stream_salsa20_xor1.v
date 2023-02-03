Require Import VST.floyd.proofauto.
Local Open Scope logic.
Require Import Coq.Lists.List. Import ListNotations.
Require Import sha.general_lemmas.

Require Import tweetnacl20140427.split_array_lemmas.
Require Import ZArith.
Local Open Scope Z. 
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
Proof. destruct (Byte.unsigned_range_2 b). specialize Byte_Int_max_unsigned; lia. Qed.

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
  rewrite Int64.signed_repr; trivial. f_equal. lia.
Qed.

Lemma sublist_hi_plus {A} (l:list A) lo a b: 0<=lo<=a -> 0<=b -> sublist lo (a + b) l =
   sublist lo a l ++ sublist a (a+b) l.
Proof. intros.
  destruct (zle (a+b) (Zlength l)).
  autorewrite with sublist; auto.
  transitivity (sublist lo (Zlength l) l).
-
  unfold sublist. f_equal.
  rewrite !firstn_same; auto.
  rewrite ZtoNat_Zlength. lia.
  rewrite <- ZtoNat_Zlength.
  apply Z_to_nat_monotone. lia.
-
  destruct (zle a (Zlength l)).
  replace (sublist a (a+b) l) with (sublist a (Zlength l) l).
  autorewrite with sublist; auto.
  unfold sublist. f_equal.
  rewrite !firstn_same; auto.
  rewrite <- ZtoNat_Zlength.
  apply Z_to_nat_monotone. lia.
  rewrite ZtoNat_Zlength. lia.
  replace (sublist a (a+b) l) with (@nil A).
  rewrite <- app_nil_end.
  unfold sublist. f_equal.
  rewrite !firstn_same; auto.
  rewrite <- ZtoNat_Zlength.
  apply Z_to_nat_monotone. lia.
  rewrite <- ZtoNat_Zlength.
  apply Z_to_nat_monotone. lia.
  unfold sublist.
  rewrite skipn_short; auto.
  rewrite firstn_same.
  rewrite <- ZtoNat_Zlength.
  apply Z_to_nat_monotone. lia.
  rewrite <- ZtoNat_Zlength.
  apply Z_to_nat_monotone. lia.
Qed.

Lemma sublist0_hi_plus {A} (l:list A) a b: 0<=a -> 0<=b -> sublist 0 (a + b) l =
   sublist 0 a l ++ sublist a (a+b) l.
Proof. intros.
  apply sublist_hi_plus; lia.
Qed.

Lemma byte_unsigned_range_3 b: 0 <= Byte.unsigned b <= Int.max_unsigned.
Proof.
  destruct (Byte.unsigned_range_2 b). unfold Byte.max_unsigned in H0; simpl in H0.
  rep_lia.
Qed.

Lemma Int_unsigned_repr_byte b: Int.unsigned (Int.repr (Byte.unsigned b)) = Byte.unsigned b.
Proof. rewrite Int.unsigned_repr. trivial. rep_lia.
Qed. 

Lemma zero_ext8_byte b: Int.zero_ext 8 (Int.repr (Byte.unsigned b)) = Int.repr (Byte.unsigned b).
Proof.
  apply zero_ext_inrange. 
  rewrite Int.unsigned_repr by rep_lia. simpl. rep_lia.
Qed.

Lemma Zlxor_range_byte b1 b2: 0<= Z.lxor (Byte.unsigned b1) (Byte.unsigned b2) <= Byte.max_unsigned.
Proof.
  destruct (Byte.unsigned_range_2 b1).
  destruct (Byte.unsigned_range_2 b2).
  split. apply Z.lxor_nonneg. lia. 
  apply Zbits.Ztestbit_le. lia. clear.
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
    destruct (zeq i 7); subst. reflexivity. lia. 
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
Proof. intros.
destruct (zeq i (hi-lo)); [ | apply Znth_sublist; lia].
subst.
assert (0 <= lo <= hi) by  lia.
clear H H1.
unfold Znth. rewrite !if_false by lia.
unfold sublist.
rewrite Z.sub_add.
rewrite nth_skipn.
replace (Z.to_nat (hi-lo) + Z.to_nat lo)%nat with (Z.to_nat hi).
f_equal.
apply firstn_same.
rewrite <- ZtoNat_Zlength.
apply Z_to_nat_monotone; auto.
rewrite <- Z2Nat.inj_add; try lia.
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
  split. apply Int64.unsigned_range. lia.
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
  rewrite Int.unsigned_repr by rep_lia. rep_lia.
+ remember (ZZ zbytes n). destruct p. symmetry in Heqp. inv H. apply IHn in Heqp. clear IHn.
  destruct Heqp.
  remember (Znth (Z.of_nat n + 8) l) as b. clear Heqb.
  specialize Byte_max_unsigned_Int_max_unsigned; intros B.
  assert (B1: Byte.max_unsigned = 255) by reflexivity.
  assert (B2: two_p 8 = 256) by reflexivity. 
  destruct (Byte.unsigned_range_2 b). 
  rewrite Int.shru_div_two_p. rewrite (Int.unsigned_repr 8) by rep_lia.
  assert (B3: 0 <= Int.unsigned i + Byte.unsigned b <= Int.max_unsigned).
    split. lia. rep_lia. 
  assert (0 <= (Int.unsigned i + Byte.unsigned b) / two_p 8 < 256).
    split. apply Z_div_pos. cbv; trivial. lia.
    apply Zdiv_lt_upper_bound. cbv; trivial. lia. 
  rewrite Int.unsigned_repr; rewrite Int.unsigned_repr; trivial. lia.
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
    lia.
  rewrite Znth_map in Vi.
  2: lia.
  inv Vi. unfold Bl2VL.
  forward.
  { entailer!.
    autorewrite with sublist in *.
    red. rewrite Int.unsigned_repr by rep_lia. rep_lia.
  } 
  simpl. rewrite Znth_map; [| lia].
    rewrite Zlength_map in L.
    rewrite Znth_map; try lia.
    rewrite Zlength_map in L.
    rewrite Znth_map; try lia. 
  forward.
  forward.
  assert (Q: Z.to_nat (i + 1 - 8) = S (Z.to_nat (i-8))).
    rewrite <- Z2Nat.inj_succ. f_equal. lia. lia.
  forward.
  assert_PROP (isptr z) as PtrZ by entailer!.
  entailer!. rewrite Q; simpl; rewrite <- HeqX; simpl.
  f_equal. assert (W:Z.of_nat (Z.to_nat (i - 8)) + 8 = i).
     rewrite Z2Nat.id; lia.
     rewrite W. f_equal.
     unfold Int.add. rewrite Int_unsigned_repr_byte. trivial.

  apply derives_refl'. f_equal.
  clear H2. unfold Bl2VL.
  rewrite Q; simpl; rewrite <- HeqX. 
  rewrite upd_Znth_map. f_equal. simpl.
  assert (W:Z.of_nat (Z.to_nat (i - 8)) + 8 = i). rewrite Z2Nat.id; lia.
  rewrite W. do 2 rewrite <- upd_Znth_map.
  rewrite Byte.unsigned_repr.
  + unfold Int.add. rewrite Int_unsigned_repr_byte.
    f_equal. unfold Int.zero_ext. f_equal. apply Zbits.equal_same_bits.
    intros j J. 
    rewrite Zbits.Zzero_ext_spec; trivial. rewrite (Zbits.Ztestbit_mod_two_p 8); trivial.
    rewrite Int.unsigned_repr; trivial.
    symmetry in HeqX. apply ZZ_is_byte in HeqX.
    destruct (Byte.unsigned_range_2 (Znth i Zi)). rep_lia. computable.
  + destruct (Z_mod_lt (Int.unsigned ui + Byte.unsigned (Znth i Zi)) 256). 
    lia. rewrite byte_unsigned_max_eq; lia.
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
        rewrite Z2Nat.inj_add, repeat_app.
        apply bxorlist_app. assumption.
        rewrite sublist_len_1. simpl. subst b. reflexivity.
        lia. lia. lia.
      - simpl in M. subst y. (*rewrite M in *;*) simpl in X; simpl.
        rewrite sublist_len_1.
        apply bxorlist_app. assumption.
        rewrite sublist_len_1. subst b. rewrite Z.add_comm. reflexivity.
        lia. lia.
      - lia.
      - lia.
      - lia.
      - lia.
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
            (Bl2VL l ++ repeat Vundef (Z.to_nat (cLen - 64))) c))).
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
                        (Bl2VL l ++ repeat Vundef (Z.to_nat (cLen - i))) c))).
{ entailer!. autorewrite with sublist.
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
        simpl. rewrite Z.max_r. lia. apply Zlength_nonneg.
        apply top_share_nonidentity.
    + apply valid_pointer_null. }
  { unfold Bl2VL in *.
    destruct mInit; simpl in *; try contradiction.
    destruct M. { subst m; simpl in H; contradiction. } 
    clear H.
    unfold message_at. simpl in M. rewrite M in *. simpl in *.
    unfold tarray.
    assert_PROP (field_compatible (Tarray tuchar (Zlength mbytes) noattr) [] (Vptr b0 i0)) by entailer!.
    erewrite (split2_data_at_Tarray_tuchar _ _ q). 2: lia. 2: unfold Bl2VL; repeat rewrite Zlength_map; trivial. 
    Intros. unfold field_address0. simpl.
    destruct (field_compatible0_dec (Tarray tuchar (Zlength mbytes) noattr)
           [ArraySubsc q] (Vptr b0 i0)).
    2:{ elim n; clear n. apply field_compatible0_cons. simpl. split; trivial. lia. }
    assert (X: 0 + 1 * q = q) by lia. rewrite X; clear X. 
    forward; unfold Bl2VL; autorewrite with sublist. 
    + entailer!. 
        apply Byte.unsigned_range_2.
    + forward. erewrite (split2_data_at_Tarray_tuchar _ (Zlength mbytes) q).
      2: lia. 2: unfold Bl2VL; repeat rewrite Zlength_map; trivial. 
      unfold field_address0. entailer!. simpl.
      autorewrite with sublist. 
         if_tac; try contradiction. rewrite Z.mul_1_l.
      cancel.
  }
  { rewrite H in *; simpl in *. 
    destruct mInit; simpl in M; try contradiction.
    destruct M as [M _]. 2: discriminate.
    forward. entailer!.
  }  
  destruct (Znth_mapVint (map Int.repr (map Byte.unsigned xbytes)) i) as  [xi Xi].
    repeat rewrite Zlength_map. lia.
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
    2:{ rewrite Zlength_Bl2VL. autorewrite with sublist. lia. }
    rewrite Zlength_Bl2VL, LL, Zminus_diag, upd_Znth0_old, sublist_repeat; try lia.
    2: autorewrite with sublist; lia.
    2: autorewrite with sublist; lia.
    simpl. thaw FR3.
    rewrite Znth_map in Xi. inv Xi. 2: repeat rewrite Zlength_map; lia.
    rewrite Znth_map. 2: lia.
    remember (Byte.xor (byte_at mInit (Zlength l+q) mbytes) 
                       (Znth (Zlength l) xbytes)) as mybyte.
    Exists (l++ [mybyte]). cancel.
    apply andp_right.
    + apply prop_right. 
      eapply (bxorlist_snoc mInit q m mybyte l); trivial; lia.
    + autorewrite with sublist.
      apply derives_refl'. f_equal. unfold Bl2VL. subst mybyte. clear.
      repeat rewrite map_app. rewrite <- app_assoc. f_equal. simpl.
      f_equal.
      repeat rewrite zero_ext_inrange; try rewrite xor_byte_int; try rewrite Int.unsigned_repr; trivial;
        try apply Byte.unsigned_range_2;
        try apply byte_unsigned_range_3.
      assert (X:cLen - Zlength l - 1 = cLen - (Zlength l + 1)) by lia.
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
                        (Bl2VL l ++ repeat Vundef (Z.to_nat (cLen - i))) c)).

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
        simpl. rewrite Z.max_r. lia. apply Zlength_nonneg.
        apply top_share_nonidentity.
    + apply valid_pointer_null. }
  { unfold Bl2VL in *.
    destruct mInit; try contradiction; simpl in M. 
    destruct M; subst. red in H; simpl in H; contradiction.
    clear H.
    unfold message_at. rewrite M in *. simpl in *.
    unfold tarray.
    assert_PROP (field_compatible (Tarray tuchar (Zlength mbytes) noattr) [] (Vptr b0 i0)) by entailer!.
    erewrite (split2_data_at_Tarray_tuchar _ _ q). 2: lia. 2: unfold Bl2VL; repeat rewrite Zlength_map; trivial. 
    Intros. unfold field_address0. simpl.
    destruct (field_compatible0_dec (Tarray tuchar (Zlength mbytes) noattr)
           [ArraySubsc q] (Vptr b0 i0)).
    2:{ elim n; clear n. apply field_compatible0_cons. simpl. split; trivial. lia. }
    assert (X: 0 + 1 * q = q) by lia. rewrite X; clear X.
    forward; unfold Bl2VL; autorewrite with sublist.
    { entailer!.
      apply Byte.unsigned_range_2.  }
    forward. entailer!.
    erewrite (split2_data_at_Tarray_tuchar _ (Zlength mbytes) q).
      2: lia. 2: unfold Bl2VL; repeat rewrite Zlength_map; trivial. 
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
    repeat rewrite Zlength_map. lia.
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
    2:{ rewrite Zlength_Bl2VL. autorewrite with sublist. lia. }
    rewrite Zlength_Bl2VL, LL, Zminus_diag, upd_Znth0_old, sublist_repeat; try lia.
    2: autorewrite with sublist; lia.
    2: autorewrite with sublist; lia.
    simpl. thaw FR3.
    rewrite Znth_map in Xi by list_solve. inv Xi.
    rewrite Znth_map by list_solve.
    remember (Byte.xor (byte_at mInit (Zlength l+q) mbytes) 
                       (Znth (Zlength l) xbytes)) as mybyte.
    Exists (l++ [mybyte]). cancel.
    apply andp_right.
    - apply prop_right. 
      eapply (bxorlist_snoc mInit q m mybyte l); trivial; lia.
    - autorewrite with sublist.
      apply derives_refl'. f_equal. unfold Bl2VL. subst mybyte. clear.
      repeat rewrite map_app. rewrite <- app_assoc. f_equal. simpl.
      f_equal.
      repeat rewrite zero_ext_inrange; try rewrite xor_byte_int; try rewrite Int.unsigned_repr; trivial;
        try apply Byte.unsigned_range_2;
        try apply byte_unsigned_range_3.
      assert (X:Int64.unsigned b - Zlength l - 1 = Int64.unsigned b - (Zlength l + 1)) by lia.
      rewrite X; trivial.
+ entailer!.
Intros l; Exists l.
rewrite Zminus_diag, repeat_0, app_nil_r.
entailer!.
Qed.
