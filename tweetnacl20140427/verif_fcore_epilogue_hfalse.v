Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import general_lemmas.

Require Import split_array_lemmas.
Require Import fragments.
Require Import ZArith. 
Require Import tweetNaclBase.
Require Import Salsa20.
Require Import verif_salsa_base.
Require Import tweetnaclVerifiableC.

Require Import spec_salsa.
Opaque Snuffle.Snuffle. Opaque prepare_data.
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.

Definition HFalse_inv l i xs ys :=
        length l = 64%nat /\
                forall ii, 0<=ii<i -> 
                  exists x_i, Znth ii (map Vint xs) Vundef = Vint x_i /\
                  exists y_i, Znth ii (map Vint ys) Vundef = Vint y_i /\
                  firstn 4 (skipn ((4*Z.to_nat ii)%nat) l) =
                  QuadByte2ValList (littleendian_invert (Int.add x_i y_i)).

Definition HFalsePostCond t y x w nonce out c k h xs ys data := 
PROP  ()
 LOCAL  ((*temp _i (Vint (Int.repr 16));*) lvar _t (tarray tuint 4) t;
 lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
 lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
 temp _k k; temp _h (Vint (Int.repr h)))
 SEP  (`(data_at Tsh (tarray tuint 16) (map Vint xs) x);
 `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
 `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
 `(CoreInSEP data (nonce, c, k));
 `(EX  l : list val,
   !!HFalse_inv l 16 xs ys && data_at Tsh (tarray tuchar 64) l out)).

Lemma verif_fcore_epilogue_hfalse Espec: forall t y x w nonce out c k h data OUT
  xs ys (ZL_X: Zlength xs = 16) (ZL_Y: Zlength ys = 16) (L_OUT: length OUT = 64%nat),
@semax Espec
  (initialized_list [_i] (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(CoreInSEP data (nonce, c, k)); `(data_at Tsh (tarray tuchar 64) OUT out)))
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 16) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _aux
                  (Ederef
                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                      (Etempvar _i tint) (tptr tuint)) tuint))
                (Ssequence
                  (Sset _aux1
                    (Ederef
                      (Ebinop Oadd (Evar _y (tarray tuint 16))
                        (Etempvar _i tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _aux
                      (Ebinop Oadd (Etempvar _aux tuint)
                        (Etempvar _aux1 tuint) tuint))
                    (Ssequence
                      (Sset _u8_aux
                        (Ebinop Oadd (Etempvar _out (tptr tuchar))
                          (Ebinop Omul (Econst_int (Int.repr 4) tint)
                            (Etempvar _i tint) tint) (tptr tuchar)))
                      (Scall None
                        (Evar _st32 (Tfunction
                                      (Tcons (tptr tuchar)
                                        (Tcons tuint Tnil)) tvoid cc_default))
                        ((Etempvar _u8_aux (tptr tuchar)) ::
                         (Etempvar _aux tuint) :: nil)))))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
(normal_ret_assert (HFalsePostCond t y x w nonce out c k h xs ys data)).
Proof. intros.
eapply semax_post'.
Focus 2.
    Opaque littleendian.
    Opaque littleendian_invert. Opaque Snuffle20. Opaque prepare_data. 
    Opaque QuadByte2ValList.
  forward_for_simple_bound 16 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP 
   (`(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(CoreInSEP data (nonce, c, k));
   `(EX l:_, !!HFalse_inv l i xs ys && data_at Tsh (tarray tuchar 64) l out)))).
  { entailer. apply (exp_right OUT). cancel. apply andp_right; try cancel.
    apply prop_right. unfold HFalse_inv. rewrite L_OUT. split; trivial; intros. omega. } 
  { rename H into I;  normalize. intros l; normalize. rename H into INV_l.
    destruct (Znth_mapVint xs i Vundef) as [xi Xi]; try omega.
    destruct (Znth_mapVint ys i Vundef) as [yi Yi]; try omega.
    forward. 
    { entailer. apply prop_right. simpl. rewrite Xi. simpl; trivial. }
    forward.
    { entailer. apply prop_right. rewrite Yi. simpl; trivial. }
    forward sum. subst sum.
    rewrite Xi, Yi. simpl. 
    Opaque Z.mul. rewrite data_at_isptr at 1. normalize. rename H into isptrOut.
    forward v.
    assert (L: length l = 64%nat). apply INV_l.
    assert (ZL: Zlength l = 64). rewrite Zlength_correct, L; simpl; trivial.
    rewrite <- ZL, (split3_offset_array_at tuchar (eq_refl _) ((4 * Z.to_nat i)%nat) 4 Tsh l).
    Focus 2. eapply Nat2Z.inj_le. rewrite Zlength_correct in ZL.
             rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id. simpl. rewrite ZL. omega. apply I.
    normalize. rename H into OIR_out0. rename H0 into OUR_out64.
    rewrite Nat2Z.inj_mul. rewrite Z2Nat.id. 2: apply I.
    assert (Z.of_nat 4 = 4). reflexivity. rewrite H; clear H.
    Opaque firstn. Opaque skipn. Opaque mult.
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
    forward_call' (offset_val (Int.repr (4 * i)) out, Int.add xi yi).
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
    { entailer. apply (exp_right (firstn 4 (skipn (4 * Z.to_nat i) l))).
      rewrite firstn_length, skipn_length, L, Min.min_l. entailer; cancel.
      apply Nat2Z.inj_le. rewrite Nat2Z.inj_sub, Nat2Z.inj_mul, Z2Nat.id. xomega. apply I.
      apply Nat2Z.inj_le. rewrite Nat2Z.inj_mul, Z2Nat.id. xomega. apply I. }

    simpl. intros. entailer.
    apply (exp_right ((firstn (4 * Z.to_nat i) l) ++
                      (QuadByte2ValList (littleendian_invert (Int.add xi yi))) ++
                      (skipn (4 * Z.to_nat i + 4) l))).
    entailer.
    unfold QByte. simpl.
    assert (LL: length
           (firstn (4 * Z.to_nat i) l ++
            QuadByte2ValList (littleendian_invert (Int.add xi yi)) ++
            skipn (4 * Z.to_nat i + 4) l) = 64%nat). 
    { do 2 rewrite app_length. 
      rewrite firstn_length, QuadByteValList_length, skipn_length, Min.min_l.
      rewrite L. rewrite plus_assoc, (plus_comm _ 4), <- le_plus_minus. trivial.
      apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id. xomega. apply I.
      apply Nat2Z.inj_le. rewrite L, Nat2Z.inj_mul, Z2Nat.id. xomega. apply I. }
    assert (ZLL: Zlength (firstn (4 * Z.to_nat i) l ++
            QuadByte2ValList (littleendian_invert (Int.add xi yi)) ++
            skipn (4 * Z.to_nat i + 4) l) = 64).
    { rewrite Zlength_correct, LL. reflexivity. } 
    apply andp_right. 
    { apply prop_right. split; trivial. intros ii II. 
      destruct INV_l as [_ INV_l].
      assert(QQ: (4 * Z.to_nat ii <= length l)%nat).
         simpl in *; rewrite L. rewrite <- (Z2Nat.inj_mul 4). apply (Z2Nat.inj_le _ 64). omega. omega. omega. omega. omega.
      destruct (zlt ii i).
        + destruct (INV_l ii) as [x_ii [Z_ii [y_ii [Y_iiA Y_iiB]]]]. omega.
          rewrite Z_ii, Y_iiA. exists x_ii; split. trivial. 
          exists y_ii; split. trivial. rewrite <- Y_iiB. clear Y_iiB. clear INV_l.
          assert (Arith: (4 * Z.to_nat i)%nat = (4 * Z.to_nat ii + 4 * Z.to_nat (i-ii))%nat).
            rewrite <- mult_plus_distr_l, Z2Nat.inj_sub, le_plus_minus_r. trivial. apply Z2Nat.inj_le. omega. omega. omega. omega.
          rewrite Arith. rewrite <- coqlib3.firstn_app. rewrite <- app_assoc.
          rewrite skipn_app2; rewrite firstn_length, Min.min_l; trivial. 2: omega.
          rewrite minus_diag, skipn_0.
          rewrite firstn_app1. rewrite <- skipn_firstn. rewrite <- Arith. 
          do 2 rewrite <- skipn_firstn. f_equal. apply coqlib3.firstn_firstn. 
           specialize (mult_plus_distr_l 4 (Z.to_nat ii) 1); rewrite mult_1_r. intros WW; rewrite <- WW; clear WW. 
            specialize (Z2Nat.inj_add ii 1); simpl.
            intros WW; rewrite <- WW; clear WW; try omega. 
            rewrite <- (Z2Nat.inj_mul 4); try omega. 
            rewrite <- (Z2Nat.inj_mul 4); try omega.
            apply Z2Nat.inj_le; omega.
           rewrite firstn_length, Min.min_l.
              rewrite <- (Z2Nat.inj_mul 4); try omega.
              apply (Z2Nat.inj_le 4); omega.
           rewrite skipn_length. simpl; rewrite L.
           rewrite Z2Nat.inj_sub, mult_minus_distr_l; try apply II. apply minus_le_compat_r.
              rewrite <- (Z2Nat.inj_mul 4); try omega. apply (Z2Nat.inj_le _ 64); omega.
       +  assert (IX: ii = i) by omega. subst ii. clear g INV_l.
          exists xi. split; trivial. exists yi; split; trivial.
          rewrite skipn_app2; rewrite firstn_length, Min.min_l; try omega.
          rewrite minus_diag, skipn_0. 
          apply hmac_pure_lemmas.firstn_exact. apply QuadByteValList_length. }
    cancel.
    rewrite <- ZLL. remember (Zlength l - Z.of_nat (4 * Z.to_nat i + 4)).
    specialize (append_split3_Tarray_at tuchar). intros DD; simpl in DD.
    unfold tarray; erewrite DD; clear DD; try reflexivity.
    rewrite ZLL. repeat rewrite Z.mul_1_l.
    repeat rewrite <- (QuadByteValList_ZLength (littlendian_invert (Int.add xi _id0))).
    assert (ZL3: Zlength (firstn (4 * Z.to_nat i) l) = (4 * i)%Z).
      rewrite Zlength_correct, firstn_length, L, Min.min_l, Nat2Z.inj_mul, Z2Nat.id. trivial. apply I.
      apply Nat2Z.inj_le. rewrite Nat2Z.inj_mul, Z2Nat.id. xomega. apply I.
    rewrite ZL3. 
    assert (ZL4: Zlength (skipn (4 * Z.to_nat i + 4) l) = z).
      rewrite Zlength_correct, skipn_length, Heqz. rewrite ZL, L. rewrite Nat2Z.inj_sub. reflexivity.
      apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id. xomega. apply I.
    rewrite ZL4. rewrite <- ZL, Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id.
       apply andp_right. apply andp_right; apply prop_right; simpl; assumption.
    rewrite <- QuadByteValList_ZLength. simpl.  cancel. apply I. }
  apply derives_refl.
unfold HFalsePostCond. entailer. apply (exp_right l); entailer.
(*With temp _i (Vint (Int.repr 16) in LOCAL of HfalsePostCond: apply derives_refl. *)
Qed.
