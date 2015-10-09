Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import general_lemmas.

Require Import split_array_lemmas.
(*Require Import fragments.*)
Require Import ZArith. 
Require Import tweetNaclBase.
Require Import Salsa20.
Require Import tweetnaclVerifiableC.
Require Import verif_salsa_base.

Require Import spec_salsa. 
Opaque Snuffle.Snuffle. Opaque prepare_data.
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.

Definition HTrue_inv1 l i ys xs : Prop :=
      Zlength l = 16 /\ exists ints, l=map Vint ints /\
               forall j, 0<=j<16 -> exists xj,
                Znth j xs Vundef = Vint xj
                /\ (j<i -> exists yj, Znth j ys Vundef = Vint yj /\
                                      Znth j l Vundef = Vint (Int.add yj xj)) 
                /\ (i<=j ->  Znth j l Vundef = Vint xj).

Lemma HTrue_loop1 Espec: forall t y x w nonce out c k h data OUT xs ys,
@semax CompSpecs Espec
  (initialized_list [_i] (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 20)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(CoreInSEP data (nonce, c, k)); `(data_at Tsh (tarray tuchar 64) OUT out)))
  (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 16) tint) tint)
     (Ssequence
        (Sset _aux
           (Ederef
              (Ebinop Oadd (Evar _y (tarray tuint 16)) (Etempvar _i tint)
                 (tptr tuint)) tuint))
        (Ssequence
           (Sset _aux1
              (Ederef
                 (Ebinop Oadd (Evar _x (tarray tuint 16)) (Etempvar _i tint)
                    (tptr tuint)) tuint))
           (Sassign
              (Ederef
                 (Ebinop Oadd (Evar _x (tarray tuint 16)) (Etempvar _i tint)
                    (tptr tuint)) tuint)
              (Ebinop Oadd (Etempvar _aux tuint) (Etempvar _aux1 tuint) tuint))))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))
  (normal_ret_assert 
   (EX  l : list val,
     PROP  (HTrue_inv1 l 16 (map Vint ys) (map Vint xs))
     LOCAL  (temp _i (Vint (Int.repr 16)); lvar _t (tarray tuint 4) t;
             lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
             lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out;
             temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
     SEP (`(data_at Tsh (tarray tuint 16) l x);
          `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
          `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
          `(CoreInSEP data (nonce, c, k)); `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. 
  intros. abbreviate_semax.
  assert_PROP (Zlength (map Vint xs) = 16). entailer. rename H into XL.
  assert_PROP (Zlength (map Vint ys) = 16). entailer. rename H into YL.
  forward_for_simple_bound 16 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(EX l:_, !!HTrue_inv1 l i (map Vint ys) (map Vint xs)
              && data_at Tsh (tarray tuint 16) l x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(CoreInSEP data (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
  { entailer. apply (exp_right (map Vint xs)).
    entailer. apply prop_right. split. assumption.
    exists xs; split; trivial.
    intros. 
    destruct (Znth_mapVint xs j Vundef) as [xj Xj]. rewrite Zlength_map in XL; omega.
    exists xj; split; trivial.
    split; intros. omega. trivial. }
  { rename H into I. normalize. intros xlist; normalize. 
    destruct H as [XLL XLIST].
    destruct XLIST as [xints [INTS J]]. subst xlist.
    destruct (J _ I) as [xi [Xi [_ HXi]]].
    destruct (Znth_mapVint ys i Vundef) as [yi Yi]. rewrite Zlength_map in YL; omega.
    forward. 
    { entailer. rewrite Yi. entailer. }
    forward.
    { entailer. rewrite HXi. entailer. omega. }
    forward. 
    entailer. rewrite Yi in H1. symmetry in H1; inv H1. rewrite Yi, HXi; simpl. 2: omega. 
    apply (exp_right (upd_Znth_in_list i (map Vint xints) (Vint (Int.add yi xi)))); entailer.
    apply prop_right.
    split.
      rewrite upd_Znth_in_list_Zlength. assumption. simpl; rewrite XLL. omega.
    eexists; split. apply upd_Znth_in_list_ints. 
    intros k K. destruct (J _ K) as [xj [Xj [IJ1 IJ2]]].
      exists xj. split. assumption.
      split; intros. 
      + destruct (zlt k i).
        - destruct (IJ1 l) as [yj [Yj Xj']]. exists yj; split; trivial.
          rewrite upd_Znth_diff; trivial. 
            simpl in *; omega.
            simpl in *; omega.
            omega.
        - assert (JJ: k=i) by omega. subst k.
          rewrite Xj in Xi; inv Xi. 
          rewrite upd_Znth_same, Yi. exists yi; split; trivial.
          simpl in *; omega.
      + rewrite upd_Znth_diff. apply IJ2; omega. 
            simpl in *; omega.
            simpl in *; omega.
            omega. }
entailer. apply (exp_right l); entailer. 
Qed.

(* Fragment:
       FOR(i,4) {
        x[5*i] -= ld32(c+4*i);
        x[6+i] -= ld32(in+4*i);
       }*)  
Fixpoint hPosLoop2 (n:nat) (sumlist: list int) (C Nonce: SixteenByte): list int :=
       match n with
         O => sumlist 
       | S m => let j:= Z.of_nat m in
                let s := hPosLoop2 m sumlist C Nonce in
                let five := Int.sub (Znth (5*j) sumlist Int.zero) (littleendian (Select16Q C j)) in
                let six := Int.sub (Znth (6+j) sumlist Int.zero) (littleendian (Select16Q Nonce j)) in
                upd_Znth_in_list (6+j) (upd_Znth_in_list (5*j) s five) six
       end.

Lemma HTrue_loop2 Espec: forall t y x w nonce out c k h OUT ys intsums Nonce C K,
@semax CompSpecs Espec 
  (initialized_list [_i] (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  ((*temp _i (Vint (Int.repr 16)); *) lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) (map Vint intsums) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(CoreInSEP(Nonce, C, K) (nonce, c, k));
   `(data_at Tsh (tarray tuchar 64) OUT out)))
   (Ssequence (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Econst_int (Int.repr 4) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _u8_aux
                      (Ebinop Oadd (Etempvar _c (tptr tuchar))
                        (Ebinop Omul (Econst_int (Int.repr 4) tint)
                          (Etempvar _i tint) tint) (tptr tuchar)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some 185%positive)
                          (Evar _ld32 (Tfunction (Tcons (tptr tuchar) Tnil)
                                        tuint cc_default))
                          ((Etempvar _u8_aux (tptr tuchar)) :: nil))
                        (Sset _aux (Etempvar 185%positive tuint)))
                      (Ssequence
                        (Sset _aux1
                          (Ederef
                            (Ebinop Oadd (Evar _x (tarray tuint 16))
                              (Ebinop Omul (Econst_int (Int.repr 5) tint)
                                (Etempvar _i tint) tint) (tptr tuint)) tuint))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _x (tarray tuint 16))
                                (Ebinop Omul (Econst_int (Int.repr 5) tint)
                                  (Etempvar _i tint) tint) (tptr tuint))
                              tuint)
                            (Ebinop Osub (Etempvar _aux1 tuint)
                              (Etempvar _aux tuint) tuint))
                          (Ssequence
                            (Sset _u8_aux
                              (Ebinop Oadd (Etempvar _in (tptr tuchar))
                                (Ebinop Omul (Econst_int (Int.repr 4) tint)
                                  (Etempvar _i tint) tint) (tptr tuchar)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some 186%positive)
                                  (Evar _ld32 (Tfunction
                                                (Tcons (tptr tuchar) Tnil)
                                                tuint cc_default))
                                  ((Etempvar _u8_aux (tptr tuchar)) :: nil))
                                (Sset _aux (Etempvar 186%positive tuint)))
                              (Ssequence
                                (Sset _aux1
                                  (Ederef
                                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                                      (Ebinop Oadd
                                        (Econst_int (Int.repr 6) tint)
                                        (Etempvar _i tint) tint)
                                      (tptr tuint)) tuint))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                                      (Ebinop Oadd
                                        (Econst_int (Int.repr 6) tint)
                                        (Etempvar _i tint) tint)
                                      (tptr tuint)) tuint)
                                  (Ebinop Osub (Etempvar _aux1 tuint)
                                    (Etempvar _aux tuint) tuint))))))))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
  (normal_ret_assert (PROP  ()
 LOCAL  (temp _i (Vint (Int.repr 4)); lvar _t (tarray tuint 4) t;
 lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
 lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
 temp _k k; temp _h (Vint (Int.repr h)))
 SEP  (`(SByte Nonce nonce); `(SByte C c); `(ThirtyTwoByte K k);
 `(data_at Tsh (tarray tuint 16) (map Vint (hPosLoop2 4 intsums C Nonce)) x);
 `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
 `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
 `(data_at Tsh (tarray tuchar 64) OUT out)))).
Proof. intros. abbreviate_semax. unfold CoreInSEP. normalize.
  assert_PROP (Zlength (map Vint ys) = 16). entailer. rename H into ZL_Y; rewrite Zlength_map in ZL_Y.
  assert_PROP (Zlength (map Vint intsums) = 16). entailer. rename H into SL; rewrite Zlength_map in SL.
  forward_for_simple_bound 4 (EX i:Z, 
  (PROP  ()
   LOCAL  ((*NOTE: we have to remove the old i here to get things to work: temp _i (Vint (Int.repr 16)); *)
           lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(SByte Nonce nonce); `(SByte C c); `(ThirtyTwoByte K k);
   `(data_at Tsh (tarray tuint 16) (map Vint (hPosLoop2 (Z.to_nat i) intsums C Nonce)) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(data_at Tsh (tarray tuchar 64) OUT out)))).
    { entailer. }
    { rename H into I.
      unfold SByte at 2. rewrite data_at_isptr with (p:=c). normalize.
      apply isptrD in Pc. destruct Pc as [cb [coff HC]]. rewrite HC in *.
      Opaque Zmult. Opaque Z.add. 

      forward.
      assert (C16:= SixteenByte2ValList_Zlength C).
      remember (SplitSelect16Q C i) as FB; destruct FB as (Front, BACK).
      specialize (Select_SplitSelect16Q C i _ _ HeqFB); intros SSS.
      assert_PROP (field_compatible (Tarray tuchar 16 noattr) [] (Vptr cb coff)). entailer.
      rename H into FC.
      destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB I) as[FL BL].

 (* An alternative to Select_Unselect_Tarray_at is to use
    (split3_data_at_Tarray_at_tuchar Tsh 16 (Zlength (QuadChunks2ValList Front)) 
        (Zlength (QuadChunks2ValList [Select16Q C i]))); trivial;
    repeat rewrite Zlength_app;
    repeat rewrite QuadChunk2ValList_ZLength;
    repeat rewrite FL; try rewrite BL; 
    try rewrite <- QuadByteValList_ZLength; try rewrite Z.mul_1_r.
    2: clear - I; omega. 2: clear - I; omega. 2: clear - I; omega. 
    2: rewrite <- HC; trivial. etc*)  
  erewrite (@Select_Unselect_Tarray_at CompSpecs 16 (Vptr cb coff)); try assumption.
      2: rewrite SSS; reflexivity.
      2: rewrite <- SSS, <- C16; trivial.
      2: rewrite <- SSS, <- C16; cbv; trivial.
  unfold Select_at. repeat rewrite QuadChunk2ValList_ZLength. rewrite Z.mul_1_r, FL.
       simpl. rewrite app_nil_r. simpl. 
       normalize.
      
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
    forward_call ((Vptr cb (Int.add coff (Int.repr (4 * i)))),
                      Select16Q C i) pat. 
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec. 
      subst pat.
      assert (PL2length: forall n, (0<=n<4)%nat -> Zlength (hPosLoop2 n intsums C Nonce) = 16).
        clear - SL.
        induction n; simpl; intros. trivial.
        repeat rewrite upd_Znth_in_list_Zlength. apply IHn; omega. omega. 
          rewrite IHn; omega. 
          rewrite IHn; omega. 
      assert (PL2Zlength: Zlength (hPosLoop2 (Z.to_nat i) intsums C Nonce) = 16).
         apply PL2length. split; try omega. apply (Z2Nat.inj_lt _ 4); omega.
        
      destruct (Znth_mapVint (hPosLoop2 (Z.to_nat i) intsums C Nonce) (5*i) Vundef) as [vj Vj].
      rewrite PL2Zlength; omega. 
      forward.
      { rewrite Vj. entailer. }
      rewrite Vj.

      forward.

      unfold SByte. rewrite data_at_isptr with (p:=nonce). normalize.
      apply isptrD in Pnonce. destruct Pnonce as [nb [noff NC]]. rewrite NC in *.
      forward.

      assert_PROP (field_compatible (Tarray tuchar 16 noattr) [] (Vptr nb noff)). entailer.
      rename H into FCN.
      assert (N16:= SixteenByte2ValList_Zlength Nonce).
      remember (SplitSelect16Q Nonce i) as FBN; destruct FBN as (FrontN, BACKN).
      specialize (Select_SplitSelect16Q Nonce i _ _ HeqFBN); intros NNN.
      unfold SByte.
      destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFBN I) as [FN BN].
      erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption.
      2: rewrite NNN; reflexivity.
      2: rewrite <- NNN, <- N16; trivial.
      2: rewrite <- NNN, <- N16; cbv; trivial.
      unfold Select_at. repeat rewrite QuadChunk2ValList_ZLength. rewrite Zmult_1_r, FN.
      simpl. rewrite app_nil_r. simpl. 
      normalize. (*rewrite Vj.*)
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
      forward_call (Vptr nb (Int.add noff (Int.repr (4 * i))),
                     Select16Q Nonce i) pat.
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
     subst pat. simpl. 
     destruct (Znth_mapVint (hPosLoop2 (Z.to_nat i) intsums C Nonce) (6+i) Vundef) as [uj Uj].
      rewrite PL2Zlength; omega.
     forward.
     { entailer. rewrite ZtoNat_Zlength in Uj, PL2Zlength.
           rewrite upd_Znth_diff. rewrite Uj. apply prop_right; trivial.
           rewrite Zlength_map, PL2Zlength; simpl; omega.
           rewrite Zlength_map, PL2Zlength; simpl; omega.
           omega. } 
     rewrite upd_Znth_diff. 
       2: rewrite Zlength_map, PL2Zlength; simpl; omega. 
       2: rewrite Zlength_map, PL2Zlength; simpl; omega. 
       2: omega.
     forward. 
(*Issue: substitution in entailer is a bit too eager here. Without the following assert (FLN: ...) ... destruct FLN,
  the two hypotheses are simply combined to Zlength Front = Zlength FrontN by entailer (and again by the inv H0) *)
     assert (FLN: Zlength Front = i /\ Zlength FrontN = i). split; assumption. clear FL FN.
     entailer. 
     rewrite Uj in H0. symmetry in H0; inv H0.
     destruct FLN as [FL FLN].

     rewrite Uj. simpl.
     cancel.
     repeat rewrite <- sepcon_assoc.
     apply sepcon_derives.
     + unfold SByte.
       erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption.
       2: rewrite NNN; reflexivity.
       erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption.
       2: rewrite SSS; reflexivity. 
       unfold Select_at. repeat rewrite QuadChunk2ValList_ZLength. rewrite FL, FLN.
        rewrite Zmult_1_r. simpl. 
        unfold QByte. repeat rewrite app_nil_r. cancel.
       rewrite <- SSS, <- C16; trivial.
       rewrite <- SSS, <- C16. cbv; trivial.
       rewrite <- NNN, <- N16; trivial.
       rewrite <- NNN, <- N16. cbv; trivial.
     + rewrite field_at_isptr. normalize. apply isptrD in Px. destruct Px as [xb [xoff XP]]. rewrite XP in *.
       rewrite field_at_data_at. unfold tarray, field_address; simpl. if_tac; try contradiction.
       rewrite Int.add_zero. 
       apply data_at_ext.
       rewrite (Zplus_comm i 1), Z2Nat.inj_add; simpl; try omega.
       rewrite Z2Nat.id.
       rewrite upd_Znth_in_list_ints.
       rewrite upd_Znth_in_list_ints. 
       unfold upd_Znth_in_list.
       assert (VJeq: vj = Znth (5 * i) intsums Int.zero). 
       { clear - Vj SL PL2length I.
         rewrite (Znth_map _ _ (5 * i) Vint) with (d':=Int.zero) in Vj. inv Vj.
         2: rewrite PL2length; try omega. Focus 2. split. apply (Z2Nat.inj_le 0); omega. apply (Z2Nat.inj_lt _ 4); omega.        
         destruct (zeq i 0); subst; simpl. trivial.
         destruct (zeq i 1); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. trivial.
         destruct (zeq i 2); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. 
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. trivial.
         destruct (zeq i 3); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. 
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. 
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. trivial.
         omega. } 
       rewrite <- VJeq, Zlength_map. trivial.
       assert (UJeq: uj = Znth (6 + i) intsums Int.zero).
       { clear - Uj SL PL2length I.
         rewrite (Znth_map _ _ (6 + i) Vint) with (d':=Int.zero) in Uj. inv Uj.
         2: rewrite PL2length; try omega. Focus 2. split. apply (Z2Nat.inj_le 0); omega. apply (Z2Nat.inj_lt _ 4); omega.        
         destruct (zeq i 0); subst; simpl. trivial.
         destruct (zeq i 1); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. trivial.
         destruct (zeq i 2); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. 
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. trivial.
         destruct (zeq i 3); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. 
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. 
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_in_list_Zlength; try omega. trivial.
         omega. }
       rewrite <- UJeq, Zlength_map. reflexivity. apply I. }
  entailer. 
Qed.

Definition UpdateOut (l: list val) (i:Z) (xi:int) :=
         (sublist 0 i l) ++ QuadByte2ValList (littleendian_invert xi) ++ sublist (i+4) (Zlength l) l.

Lemma UpdateOut_Zlength l i xi: 0<=i -> i + 4 <= Zlength l -> Zlength (UpdateOut l i xi) = Zlength l.
Proof. intros. unfold UpdateOut. repeat rewrite Zlength_app.
  repeat rewrite Zlength_sublist; try omega.
  rewrite <- QuadByteValList_ZLength. omega.
Qed. 

Fixpoint hPosLoop3 (n:nat) (xlist: list int) (old: list val): list val :=
    match n with 
      O => old
    | S m => let j:= Z.of_nat m in
                let s := hPosLoop3 m xlist old in
                let five := Znth (5*j) xlist Int.zero in
                let six := Znth (6+j) xlist Int.zero in
                UpdateOut (UpdateOut s (4*j) five) (16+4*j) six
       end.

Lemma hposLoop3_length xlist old: forall n, (16+4*Z.of_nat n<Zlength old) ->
        Zlength (hPosLoop3 n xlist old) = Zlength old. 
  Proof. induction n; simpl; intros. trivial.
    rewrite Zpos_P_of_succ_nat in H.
    repeat rewrite UpdateOut_Zlength.
      apply IHn. omega.
    omega. 
    simpl. rewrite IHn. omega. omega.
    omega. 
    simpl. rewrite IHn. omega. omega.
    omega. 
    simpl. rewrite IHn. omega. omega. 
  Qed.

Lemma HTrue_loop3 Espec t y x w nonce out c k h OUT xs ys Nonce C K:
@semax CompSpecs Espec 
  (initialized_list [_i] (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(SByte Nonce nonce); `(SByte C c);
   `(ThirtyTwoByte K k);
   `(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(data_at Tsh (tarray tuchar 64) OUT out)))
  (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 4) tint) tint)
     (Ssequence
        (Sset _aux
           (Ederef
              (Ebinop Oadd (Evar _x (tarray tuint 16))
                 (Ebinop Omul (Econst_int (Int.repr 5) tint)
                    (Etempvar _i tint) tint) (tptr tuint)) tuint))
        (Ssequence
           (Sset _u8_aux
              (Ebinop Oadd (Etempvar _out (tptr tuchar))
                 (Ebinop Omul (Econst_int (Int.repr 4) tint)
                    (Etempvar _i tint) tint) (tptr tuchar)))
           (Ssequence
              (Scall None
                 (Evar _st32
                    (Tfunction (Tcons (tptr tuchar) (Tcons tuint Tnil)) tvoid
                       cc_default))
                 [Etempvar _u8_aux (tptr tuchar); Etempvar _aux tuint])
              (Ssequence
                 (Sset _aux
                    (Ederef
                       (Ebinop Oadd (Evar _x (tarray tuint 16))
                          (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                             (Etempvar _i tint) tint) (tptr tuint)) tuint))
                 (Ssequence
                    (Sset _u8_aux
                       (Ebinop Oadd
                          (Ebinop Oadd (Etempvar _out (tptr tuchar))
                             (Econst_int (Int.repr 16) tint) (tptr tuchar))
                          (Ebinop Omul (Econst_int (Int.repr 4) tint)
                             (Etempvar _i tint) tint) (tptr tuchar)))
                    (Scall None
                       (Evar _st32
                          (Tfunction (Tcons (tptr tuchar) (Tcons tuint Tnil))
                             tvoid cc_default))
                       [Etempvar _u8_aux (tptr tuchar); Etempvar _aux tuint]))))))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))
(normal_ret_assert (
  PROP  ()
  LOCAL  (lvar _t (tarray tuint 4) t;
          lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
          lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
          temp _k k; temp _h (Vint (Int.repr h)))
  SEP (`(SByte Nonce nonce); `(SByte C c); `(ThirtyTwoByte K k);
       `(data_at Tsh (tarray tuint 16) (map Vint xs) x);
       `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
       `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
       `(data_at Tsh (tarray tuchar 64) (hPosLoop3 4 xs OUT) out)))).
Proof. intros. abbreviate_semax.
 assert_PROP (Zlength (map Vint xs) = 16). entailer. rename H into ZL_X; rewrite Zlength_map in ZL_X.
 assert_PROP (Zlength OUT = 64). entailer. rename H into OL.
 forward_for_simple_bound 4 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(SByte Nonce nonce); `(SByte C c); `(ThirtyTwoByte K k);
   `(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(data_at Tsh (tarray tuchar 64) (hPosLoop3 (Z.to_nat i) xs OUT) out)))).
    { entailer. }
  { rename H into I. 

    assert (P3_Zlength: Zlength (hPosLoop3 (Z.to_nat i) xs OUT) = 64).
      rewrite hposLoop3_length. assumption. rewrite OL, Z2Nat.id; omega.
    assert (P3_length: length (hPosLoop3 (Z.to_nat i) xs OUT) = 64%nat).
      rewrite <- ZtoNat_Zlength, P3_Zlength; reflexivity.
    remember (hPosLoop3 (Z.to_nat i) xs OUT) as ll. (*clear Heqll.*)
      
    destruct (Znth_mapVint xs (5 * i) Vundef) as [xi Xi]. omega.
    forward.
    { entailer. rewrite Xi. entailer. }
    rewrite Xi.
    rewrite data_at_isptr with (p:=out). normalize.
    apply isptrD in Pout. destruct Pout as [ob [ooff OC]]. rewrite OC in *.
    forward. 
    assert_PROP(field_compatible (Tarray tuchar 64 noattr) [] (Vptr ob ooff)). entailer.
    rename H into FCO.
    rewrite <- P3_Zlength.
    rewrite (split3_data_at_Tarray_at_tuchar Tsh (Zlength ll) (4 *i) 4); try rewrite P3_Zlength; trivial; try omega. 
    unfold at_offset at 1.
    normalize.
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
    forward_call (offset_val (Int.repr (4 * i)) (Vptr ob ooff), xi).
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
    { entailer.
      apply (exp_right (sublist (4 * i) (4 + 4 * i) ll)).
      entailer. cancel. }
    normalize. Opaque mult. 
    assert (Upd_ll_Zlength: Zlength (UpdateOut ll (4 * i) xi) = 64).
      rewrite UpdateOut_Zlength; trivial. omega. omega.
    apply semax_pre with (P':=
  (PROP  ()
   LOCAL  (temp _u8_aux (Vptr ob (Int.add ooff (Int.repr (4 * i))));
   temp _aux (Vint xi); temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out (Vptr ob ooff); temp _c c; temp _k k;
   temp _h (Vint (Int.repr h)))
   SEP 
   (`(data_at Tsh (tarray tuchar 64) (UpdateOut ll (4*i) xi) (Vptr ob ooff));
   `(SByte Nonce nonce); `(SByte C c); `(ThirtyTwoByte K k);
   `(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w)))).
    { clear Heqll. Opaque Zminus. entailer. cancel. unfold QByte.
      rewrite <- Upd_ll_Zlength.
      erewrite (append_split3_data_at_Tarray_at_tuchar' Tsh  (UpdateOut ll (4 * i) _id0)); try rewrite UpdateOut_Zlength, P3_Zlength; try omega.
       2: reflexivity.
       2: cbv; trivial.
       2: assumption.
      unfold at_offset.
      rewrite <- QuadByteValList_ZLength. repeat rewrite Zlength_sublist; try omega.
      rewrite P3_Zlength, Zminus_0_r, (Zplus_comm 4).  cancel. }
 
    destruct (Znth_mapVint xs (6+i) Vundef) as [zi Zi]. omega.
    forward.
    { entailer. rewrite Zi. apply prop_right; trivial. }
    rewrite Zi.
    forward. 
    erewrite (split3_data_at_Tarray_at_tuchar Tsh 64 (16 + 4 *i) 4); trivial; try omega.
    unfold at_offset at 1. 
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
    forward_call (offset_val (Int.repr (16 + 4 * i)) (Vptr ob ooff), zi).
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
    { entailer. 
      apply (exp_right (sublist (16 + 4 * i) (4 + (16 + 4 * i)) (UpdateOut ll (4 * i) xi))).
      entailer. cancel. }
    normalize. entailer. cancel.
    assert (AA:  Z.to_nat (i + 1) = S (Z.to_nat i)).
      rewrite (Z.add_comm _ 1), Z2Nat.inj_add. simpl. apply NPeano.Nat.add_1_l. omega. omega.
    rewrite AA. simpl. 
    clear H10 H13 TC TC0 TC1 TC2 TC3 H7.
    remember (hPosLoop3 (Z.to_nat i) xs OUT) as ll; clear Heqll.
    assert (XXi: xi = Znth (5 * i) xs Int.zero).
      rewrite Znth_map' with (d':=Int.zero) in Xi; try omega. clear -Xi. inv Xi. trivial.
    assert (ZZi: _id0 = Znth (6 + i) xs Int.zero).
      rewrite Znth_map' with (d':=Int.zero) in Zi; try omega. clear -Zi. inv Zi. trivial.
    rewrite Z2Nat.id, <- XXi, <- ZZi; try omega; clear XXi ZZi.
    unfold QByte.
    remember (UpdateOut ll (4 * i) xi) as l.
    assert (ZLU: Zlength(UpdateOut l (16 + 4 * i) _id0) = 64).
      rewrite UpdateOut_Zlength; trivial. omega. omega.
    rewrite <- ZLU.
    erewrite (append_split3_data_at_Tarray_at_tuchar' Tsh  (UpdateOut l (16 + 4 * i) _id0)); 
      try rewrite ZLU; try rewrite P3_Zlength; try omega; try reflexivity; trivial.
    unfold at_offset.
    repeat rewrite Zlength_sublist; try omega. 
    rewrite <- QuadByteValList_ZLength, Upd_ll_Zlength, Zminus_0_r, (Zplus_comm 4). cancel. }
entailer. (*With temp _i (Vint (Int.repr 4)) in LOCAL of HTruePostCondL apply derives_refl.*)
Qed.

Lemma hposLoop2_Zlength16 C N l (L:Zlength l = 16): forall n, 
      5 * Z.of_nat n < 16-> 6+ Z.of_nat n < 16 -> Zlength (hPosLoop2 (S n) l C N) = 16.
Proof. intros. simpl. 
  induction n; simpl; intros; trivial.
  rewrite upd_Znth_in_list_Zlength; rewrite upd_Znth_in_list_Zlength; omega. 
  rewrite Nat2Z.inj_succ in *.
  rewrite upd_Znth_in_list_Zlength; rewrite upd_Znth_in_list_Zlength; rewrite IHn; simpl; try omega. 
  rewrite Zpos_P_of_succ_nat. omega.
  rewrite Zpos_P_of_succ_nat. omega.
  rewrite Zpos_P_of_succ_nat. omega.
Qed.

Definition HTruePostCond t y x w nonce out c k h (xs:list int) ys Nonce C K OUT := 
(EX intsums:_,
  PROP (Zlength intsums = 16 /\
        (forall j, 0 <= j < 16 -> 
           exists xj, exists yj, 
           Znth j (map Vint xs) Vundef = Vint xj /\
           Znth j (map Vint ys) Vundef = Vint yj /\
           Znth j (map Vint intsums) Vundef = Vint (Int.add yj xj)))
  LOCAL (lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
  SEP (`(SByte Nonce nonce); `(SByte C c);
       `(ThirtyTwoByte K k);
       `(data_at Tsh (tarray tuint 16)
         (map Vint (hPosLoop2 4 intsums C Nonce)) x);
       `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
       `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
       `(data_at Tsh (tarray tuchar 64)
          (hPosLoop3 4 (hPosLoop2 4 intsums C Nonce) OUT) out))).

Lemma verif_fcore_epilogue_htrue Espec t y x w nonce out c k h OUT xs ys Nonce C K:
@semax CompSpecs Espec
  (initialized_list [_i] (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs))
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 20)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (`(data_at Tsh (tarray tuint 16) (map Vint xs) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(CoreInSEP (Nonce, C, K) (nonce, c, k)); `(data_at Tsh (tarray tuchar 64) OUT out)))
        (Ssequence
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
                      (Ebinop Oadd (Evar _y (tarray tuint 16))
                        (Etempvar _i tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _aux1
                      (Ederef
                        (Ebinop Oadd (Evar _x (tarray tuint 16))
                          (Etempvar _i tint) (tptr tuint)) tuint))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _x (tarray tuint 16))
                          (Etempvar _i tint) (tptr tuint)) tuint)
                      (Ebinop Oadd (Etempvar _aux tuint)
                        (Etempvar _aux1 tuint) tuint)))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Econst_int (Int.repr 4) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _u8_aux
                      (Ebinop Oadd (Etempvar _c (tptr tuchar))
                        (Ebinop Omul (Econst_int (Int.repr 4) tint)
                          (Etempvar _i tint) tint) (tptr tuchar)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some 185%positive)
                          (Evar _ld32 (Tfunction (Tcons (tptr tuchar) Tnil)
                                        tuint cc_default))
                          ((Etempvar _u8_aux (tptr tuchar)) :: nil))
                        (Sset _aux (Etempvar 185%positive tuint)))
                      (Ssequence
                        (Sset _aux1
                          (Ederef
                            (Ebinop Oadd (Evar _x (tarray tuint 16))
                              (Ebinop Omul (Econst_int (Int.repr 5) tint)
                                (Etempvar _i tint) tint) (tptr tuint)) tuint))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _x (tarray tuint 16))
                                (Ebinop Omul (Econst_int (Int.repr 5) tint)
                                  (Etempvar _i tint) tint) (tptr tuint))
                              tuint)
                            (Ebinop Osub (Etempvar _aux1 tuint)
                              (Etempvar _aux tuint) tuint))
                          (Ssequence
                            (Sset _u8_aux
                              (Ebinop Oadd (Etempvar _in (tptr tuchar))
                                (Ebinop Omul (Econst_int (Int.repr 4) tint)
                                  (Etempvar _i tint) tint) (tptr tuchar)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some 186%positive)
                                  (Evar _ld32 (Tfunction
                                                (Tcons (tptr tuchar) Tnil)
                                                tuint cc_default))
                                  ((Etempvar _u8_aux (tptr tuchar)) :: nil))
                                (Sset _aux (Etempvar 186%positive tuint)))
                              (Ssequence
                                (Sset _aux1
                                  (Ederef
                                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                                      (Ebinop Oadd
                                        (Econst_int (Int.repr 6) tint)
                                        (Etempvar _i tint) tint)
                                      (tptr tuint)) tuint))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                                      (Ebinop Oadd
                                        (Econst_int (Int.repr 6) tint)
                                        (Etempvar _i tint) tint)
                                      (tptr tuint)) tuint)
                                  (Ebinop Osub (Etempvar _aux1 tuint)
                                    (Etempvar _aux tuint) tuint))))))))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Econst_int (Int.repr 4) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _aux
                      (Ederef
                        (Ebinop Oadd (Evar _x (tarray tuint 16))
                          (Ebinop Omul (Econst_int (Int.repr 5) tint)
                            (Etempvar _i tint) tint) (tptr tuint)) tuint))
                    (Ssequence
                      (Sset _u8_aux
                        (Ebinop Oadd (Etempvar _out (tptr tuchar))
                          (Ebinop Omul (Econst_int (Int.repr 4) tint)
                            (Etempvar _i tint) tint) (tptr tuchar)))
                      (Ssequence
                        (Scall None
                          (Evar _st32 (Tfunction
                                        (Tcons (tptr tuchar)
                                          (Tcons tuint Tnil)) tvoid
                                        cc_default))
                          ((Etempvar _u8_aux (tptr tuchar)) ::
                           (Etempvar _aux tuint) :: nil))
                        (Ssequence
                          (Sset _aux
                            (Ederef
                              (Ebinop Oadd (Evar _x (tarray tuint 16))
                                (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                                  (Etempvar _i tint) tint) (tptr tuint))
                              tuint))
                          (Ssequence
                            (Sset _u8_aux
                              (Ebinop Oadd
                                (Ebinop Oadd (Etempvar _out (tptr tuchar))
                                  (Econst_int (Int.repr 16) tint)
                                  (tptr tuchar))
                                (Ebinop Omul (Econst_int (Int.repr 4) tint)
                                  (Etempvar _i tint) tint) (tptr tuchar)))
                            (Scall None
                              (Evar _st32 (Tfunction
                                            (Tcons (tptr tuchar)
                                              (Tcons tuint Tnil)) tvoid
                                            cc_default))
                              ((Etempvar _u8_aux (tptr tuchar)) ::
                               (Etempvar _aux tuint) :: nil))))))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))))
(normal_ret_assert (HTruePostCond t y x w nonce out c k h xs ys Nonce C K OUT)).
Proof. intros.
forward_seq. apply HTrue_loop1; trivial.
apply extract_exists_pre; intros sums. normalize. 
destruct H as [SL [intsums [? HSums1]]]; subst sums. rewrite Zlength_map in SL.
forward_seq.
  eapply semax_pre. 
   2: apply (HTrue_loop2 Espec t y x w nonce out c k h OUT ys intsums Nonce C K); assumption.
   entailer. 
eapply semax_pre_post.
  Focus 3. apply (HTrue_loop3 Espec t y x w nonce out c k h OUT 
            (hPosLoop2 4 intsums C Nonce) ys Nonce C K); try assumption.
  entailer. 
unfold POSTCONDITION, abbreviate, HTruePostCond. Opaque ThirtyTwoByte. Opaque hPosLoop2. Opaque hPosLoop3.
intros. entailer. simpl. apply normal_ret_assert_derives.
apply (exp_right intsums). entailer.
apply prop_right. clear - HSums1 SL. intros.
  destruct (HSums1 _ H) as [xj [Xj [X _]]].
  destruct X as [yj [Yi Sj]]. apply H.
  exists xj, yj. auto.
Qed.