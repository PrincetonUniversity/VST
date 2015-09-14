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

Definition HTrue_inv1 l i ys xs : Prop :=
      Zlength l = 16 /\ exists ints, l=map Vint ints /\
               forall j, 0<=j<16 -> exists xj,
                Znth j xs Vundef = Vint xj
                /\ (j<i -> exists yj, Znth j ys Vundef = Vint yj /\
                                      Znth j l Vundef = Vint (Int.add yj xj)) 
                /\ (i<=j ->  Znth j l Vundef = Vint xj).

Lemma HTrue_loop1 Espec: forall t y x w nonce out c k h data OUT
  xs ys (ZL_X: Zlength xs = 16) (ZL_Y: Zlength ys = 16),
@semax Espec
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
Proof. intros.
  forward_for_simple_bound 16 (EX i:Z, 
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
      lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
      temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP 
   (`(EX l:_, !!HTrue_inv1 l i (map Vint ys) (map Vint xs)
              && data_at Tsh (tarray tuint 16) l x);
    `(data_at Tsh (tarray tuint 16) (map Vint ys)  y);
    `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
    `(CoreInSEP data (nonce, c, k));
    `(data_at Tsh (tarray tuchar 64) OUT out)))).
  { entailer. apply (exp_right (map Vint xs)).
    entailer. apply prop_right. split. rewrite Zlength_map; assumption.
    exists xs; split; trivial.
    intros. 
    destruct (Znth_mapVint xs j Vundef) as [xj Xj]. omega.
    exists xj; split; trivial.
    split; intros. omega. trivial. }
  { rename H into I. normalize. intros xlist; normalize. 
    destruct H as [XL XLIST].
    destruct XLIST as [xints [INTS J]]. subst xlist.
    destruct (J _ I) as [xi [Xi [_ HXi]]].
    destruct (Znth_mapVint ys i Vundef) as [yi Yi]. omega.
    forward.
    { entailer. rewrite Yi. entailer. }
    forward.
    { entailer. rewrite HXi. entailer. omega. }
    forward. 
    entailer. rewrite Yi in H1. symmetry in H1; inv H1. rewrite Yi, HXi; simpl. 2: omega. 
    apply (exp_right (upd_reptype_array tuint i (map Vint xints) (Vint (Int.add yi xi)))); entailer.
    apply prop_right.
    split.
      rewrite (upd_reptype_array_Zlength tuint). assumption. simpl; rewrite XL. omega.
    eexists; split. apply (upd_reptype_ints i xints (Int.add yi xi)).
      rewrite <- ZtoNat_Zlength. apply Z2Nat.inj_lt. omega.
      rewrite Zlength_map in XL; omega. rewrite Zlength_map in XL; omega.
    intros. destruct (J _ H1) as [xj [Xj [IJ1 IJ2]]].
      exists xj. split. assumption.
      split; intros. 
      + destruct (zlt j i).
        - destruct (IJ1 l) as [yj [Yj Xj']]. exists yj; split; trivial.
          rewrite (upd_Znth_diff tuint); trivial. 
            simpl in *; omega.
            simpl in *; omega.
            omega.
        - assert (JJ: j=i) by omega. subst j.
          rewrite Xj in Xi; inv Xi. 
          rewrite (upd_Znth_same tuint), Yi. exists yi; split; trivial.
          simpl in *; omega.
      + rewrite (upd_Znth_diff tuint). apply IJ2; omega. 
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
                upd_intlist (6+j) (upd_intlist (5*j) s five) six
       end.

Lemma HTrue_loop2 Espec: forall t y x w nonce out c k h OUT
  ys intsums Nonce C K (ZL_Y: Zlength ys = 16) (SL : Zlength intsums = 16),
@semax Espec 
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
(Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 4) tint) tint)
     (Ssequence
        (Sset _u8_aux
           (Ebinop Oadd (Etempvar _c (tptr tuchar))
              (Ebinop Omul (Econst_int (Int.repr 4) tint) (Etempvar _i tint)
                 tint) (tptr tuchar)))
        (Ssequence
           (Ssequence
              (Scall (Some _aux'8)
                 (Evar _ld32
                    (Tfunction (Tcons (tptr tuchar) Tnil) tuint cc_default))
                 [Etempvar _u8_aux (tptr tuchar)])
              (Sset _aux (Etempvar _aux'8 tuint)))
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
                             (Etempvar _i tint) tint) (tptr tuint)) tuint)
                    (Ebinop Osub (Etempvar _aux1 tuint) (Etempvar _aux tuint)
                       tuint))
                 (Ssequence
                    (Sset _u8_aux
                       (Ebinop Oadd (Etempvar _in (tptr tuchar))
                          (Ebinop Omul (Econst_int (Int.repr 4) tint)
                             (Etempvar _i tint) tint) (tptr tuchar)))
                    (Ssequence
                       (Ssequence
                          (Scall (Some _aux'9)
                             (Evar _ld32
                                (Tfunction (Tcons (tptr tuchar) Tnil) tuint
                                   cc_default))
                             [Etempvar _u8_aux (tptr tuchar)])
                          (Sset _aux (Etempvar _aux'9 tuint)))
                       (Ssequence
                          (Sset _aux1
                             (Ederef
                                (Ebinop Oadd (Evar _x (tarray tuint 16))
                                   (Ebinop Oadd
                                      (Econst_int (Int.repr 6) tint)
                                      (Etempvar _i tint) tint) (tptr tuint))
                                tuint))
                          (Sassign
                             (Ederef
                                (Ebinop Oadd (Evar _x (tarray tuint 16))
                                   (Ebinop Oadd
                                      (Econst_int (Int.repr 6) tint)
                                      (Etempvar _i tint) tint) (tptr tuint))
                                tuint)
                             (Ebinop Osub (Etempvar _aux1 tuint)
                                (Etempvar _aux tuint) tuint)))))))))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))
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
Proof. intros. unfold CoreInSEP. normalize.
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
      apply isptrD in H. destruct H as [cb [coff HC]]. rewrite HC in *.
      Opaque Zmult. Opaque Z.add. 
      forward v.
      assert (C16:= SixteenByte2ValList_Zlength C).
      remember (SplitSelect16Q C i) as FB; destruct FB as (Front, BACK).
      specialize (Select_SplitSelect16Q C i _ _ HeqFB); intros SSS.
      erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption.
      2: rewrite SSS; reflexivity.
      normalize.
      unfold Select_at. repeat rewrite QuadChunk2ValList_ZLength.
      rewrite (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB); trivial.
      assert (LL: Zlength [Select16Q C i] = 1) by reflexivity. rewrite LL, Zmult_1_r. 
       simpl. rewrite app_nil_r. simpl. rewrite Zmult_1_l. 
      simpl. normalize.
      
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
      (*TODO: forward_call' leaves delete-temp_from_locals_side conditions here*)
      forward_call ((Vptr cb (Int.add coff (Int.repr (4 * i)))),
                      Select16Q C i).
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
      { assert (FR: Frame = [`(Unselect_at tuchar Tsh (QuadChunks2ValList Front)
                            (QuadChunks2ValList [Select16Q C i]) (QuadChunks2ValList BACK) c);
                             `(SByte Nonce nonce); `(ThirtyTwoByte K k);
                             `(data_at Tsh (tarray tuint 16) (map Vint
                               (hPosLoop2 (Z.to_nat i) intsums C Nonce)) x);
                             `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
                             `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
                             `(data_at Tsh (tarray tuchar 64) OUT out)]).
          subst Frame. reflexivity.
        subst Frame; clear FR. entailer. rewrite app_nil_r. cancel. }
      { repeat econstructor. }
   
      after_call. simpl. rewrite app_nil_r. 
      assert (PL2length: forall n, (0<=n<4)%nat -> length (hPosLoop2 n intsums C Nonce) = 16%nat).
        clear - SL.
        induction n; simpl; intros. rewrite <- ZtoNat_Zlength, SL. reflexivity. 
        repeat rewrite upd_intlist_length. apply IHn; omega. omega. 
          rewrite IHn. apply (Z2Nat.inj_lt _ 16); try omega. omega. omega.
          rewrite IHn. apply (Z2Nat.inj_lt _ 16); try omega. omega. omega.
          rewrite IHn. apply (Z2Nat.inj_lt _ 16); try omega. omega. 
      assert (PL2Zlength: Zlength (hPosLoop2 (Z.to_nat i) intsums C Nonce) = 16).
         rewrite Zlength_correct, PL2length. reflexivity. split; try omega. apply (Z2Nat.inj_lt _ 4); omega.
(*TODO: ERROR IN FLOYD: why is a `() term about result1 left unsimplified in LOCAL here?*)
      apply semax_pre with (P':=
  (PROP  ()
   LOCAL  (temp _u8_aux (Vptr cb (Int.add coff (Int.repr (4 * i))));
   temp _i (Vint (Int.repr i)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out;
   temp _c (Vptr cb coff); temp _k k; temp _h (Vint (Int.repr h));
   temp _aux (Vint (littleendian (Select16Q C i))))
   SEP 
   (`(QByte (Select16Q C i) (Vptr cb (Int.add coff (Int.repr (4 * i)))));
   `(Unselect_at tuchar Tsh (QuadChunks2ValList Front)
       (QuadByte2ValList (Select16Q C i)) (QuadChunks2ValList BACK) c);
   `(SByte Nonce nonce); `(ThirtyTwoByte K k);
   `(data_at Tsh (tarray tuint 16)
       (map Vint (hPosLoop2 (Z.to_nat i) intsums C Nonce)) x);
   `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(data_at Tsh (tarray tuchar 64) OUT out)))). entailer.
        
      destruct (Znth_mapVint (hPosLoop2 (Z.to_nat i) intsums C Nonce) (5*i) Vundef) as [vj Vj].
      rewrite PL2Zlength; omega.

      forward v1.
      { entailer. rewrite Vj. entailer. }
      rewrite Vj. forward.

      unfold SByte. rewrite data_at_isptr with (p:=nonce). normalize.
      apply isptrD in H. destruct H as [nb [noff NC]]. rewrite NC in *.
      forward v2. subst v2.

      assert (N16:= SixteenByte2ValList_Zlength Nonce).
      remember (SplitSelect16Q Nonce i) as FBN; destruct FBN as (FrontN, BACKN).
      specialize (Select_SplitSelect16Q Nonce i _ _ HeqFBN); intros NNN.
      unfold SByte. erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption.
      2: rewrite NNN; reflexivity.
      normalize.
      unfold Select_at. repeat rewrite QuadChunk2ValList_ZLength.
      rewrite (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFBN); trivial.
      assert (LN: Zlength [Select16Q Nonce i] = 1) by reflexivity. rewrite LN, Zmult_1_r.

Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
      (*TODO: forward_call' leaves delete-temp_from_locals_side conditions here*)
      forward_call ((offset_val (Int.repr (sizeof tuchar * (4 * i))) (Vptr nb noff)),
                     Select16Q Nonce i).
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
      { assert (FR: Frame = [`(Unselect_at tuchar Tsh (QuadChunks2ValList FrontN)
                               (QuadChunks2ValList [Select16Q Nonce i]) (QuadChunks2ValList BACKN) nonce);
                             `(QByte (Select16Q C i) (offset_val (Int.repr (4 * i)) c));
                             `(Unselect_at tuchar Tsh (QuadChunks2ValList Front)
                                  (QuadByte2ValList (Select16Q C i)) (QuadChunks2ValList BACK) c);
                             `(data_at Tsh (tarray tuint 16)
                                  (upd_reptype_array tuint (5 * i) (map Vint (hPosLoop2 (Z.to_nat i) intsums C Nonce)) (*l*)
                                  (Vint (Int.sub vj (littleendian (Select16Q C i))))) x);
                             `(ThirtyTwoByte K k);
                             `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
                             `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
                             `(data_at Tsh (tarray tuchar 64) OUT out)]).
          subst Frame. reflexivity.
        subst Frame; clear FR. entailer. rewrite app_nil_r. cancel. }
      { repeat econstructor. }
   
      after_call. (*AGAIN, we simplify manually some spurious `() stuff from LOCAL*) normalize. subst x1. 
      apply semax_pre with (P':=
  (PROP  ()
   LOCAL  (temp _u8_aux (Vptr nb (Int.add noff (Int.repr (4 * i))));
   temp _aux1 (Vint vj); temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w;
   temp _in (Vptr nb noff); temp _out out; temp _c (Vptr cb coff); temp _k k;
   temp _h (Vint (Int.repr h));
   temp _aux (Vint (littleendian (Select16Q Nonce i))))
   SEP 
   (`(QByte (Select16Q Nonce i)
        (offset_val (Int.repr (4 * i)) (Vptr nb noff)));
   `(Unselect_at tuchar Tsh (QuadChunks2ValList FrontN)
       (QuadChunks2ValList [Select16Q Nonce i]) (QuadChunks2ValList BACKN)
       nonce); `(QByte (Select16Q C i) (offset_val (Int.repr (4 * i)) c));
   `(Unselect_at tuchar Tsh (QuadChunks2ValList Front)
       (QuadByte2ValList (Select16Q C i)) (QuadChunks2ValList BACK) c);
   `(data_at Tsh (tarray tuint 16)
       (upd_reptype_array tuint (5 * i)
          (map Vint (hPosLoop2 (Z.to_nat i) intsums C Nonce))
          (Vint (Int.sub vj (littleendian (Select16Q C i))))) x);
   `(ThirtyTwoByte K k); `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
   `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
   `(data_at Tsh (tarray tuchar 64) OUT out)))). entailer.

     simpl. rewrite app_nil_r. 
     destruct (Znth_mapVint (hPosLoop2 (Z.to_nat i) intsums C Nonce) (6+i) Vundef) as [uj Uj].
      rewrite PL2Zlength; omega.
     forward v3.
     { entailer. apply prop_right.
           rewrite (upd_Znth_diff tuint). simpl; rewrite Uj. simpl; trivial.
           rewrite Zlength_map, PL2Zlength; simpl; omega.
           rewrite Zlength_map, PL2Zlength; simpl; omega.
           omega. } 
     subst v3.
     rewrite (upd_Znth_diff tuint). 
       2: rewrite Zlength_map, PL2Zlength; simpl; omega. 
       2: rewrite Zlength_map, PL2Zlength; simpl; omega. 
       2: omega.
     forward. 
     entailer. rewrite Uj in H0. symmetry in H0; inv H0. rewrite Uj. simpl.
     cancel.
     repeat rewrite <- sepcon_assoc.
     apply sepcon_derives.
     + unfold SByte.
       erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption.
       2: rewrite NNN; reflexivity.
       erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption.
       2: rewrite SSS; reflexivity. 
       unfold Select_at. repeat rewrite QuadChunk2ValList_ZLength.
        rewrite (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFBN); trivial.
        rewrite (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB); trivial.
        rewrite LN, LL, Zmult_1_r. simpl. rewrite Zmult_1_l.
        unfold QByte. repeat rewrite app_nil_r. cancel.
     + unfold tarray. apply derives_refl'. erewrite data_at_Tarray_ext. reflexivity.
       intros j J. rewrite (Zplus_comm i 1). rewrite Z2Nat.inj_add; simpl; try omega. 
       rewrite Z2Nat.id; try omega. 
       clear H1 H2 H3 H4 H5 H6 H7 H8 H9 TC0 TC1 TC2 TC3 TC.
       assert (upd_reptype_array tuint (6 + i)
        (upd_reptype_array tuint (5 * i)
           (map Vint (hPosLoop2 (Z.to_nat i) intsums C Nonce))
           (Vint (Int.sub vj (littleendian (Select16Q C i)))))
        (Vint (Int.sub uj (littleendian (Select16Q Nonce i)))) 
       = map Vint
        (upd_intlist (6 + i)
           (upd_intlist (5 * i) (hPosLoop2 (Z.to_nat i) intsums C Nonce)
              (Int.sub (Znth (5 * i) intsums Int.zero)
                 (littleendian (Select16Q C i))))
           (Int.sub (Znth (6 + i) intsums Int.zero)
              (littleendian (Select16Q Nonce i))))).
       { assert (Znth (6 + i) intsums Int.zero = uj).
         + clear - I Uj PL2length SL. unfold Znth in *.
           destruct (zlt (6 + i) 0); subst; simpl in *. omega. 
           rewrite nth_map' with (d':=Int.zero) in Uj.
           Focus 2. rewrite PL2length. apply (Z2Nat.inj_lt _ 16); omega.
                    split; try omega. apply (Z2Nat.inj_lt _ 4); omega.
           inversion Uj; clear Uj. clear H0.
           destruct (zeq i 0); subst; simpl. trivial.
           assert (X: (Z.to_nat (5 * 0) < length intsums)%nat).
              rewrite Z2Nat.inj_mul, <- ZtoNat_Zlength, SL; simpl; omega. 
           assert (Y: (Z.to_nat (6 + 0) < length intsums)%nat).
              rewrite Z2Nat.inj_add, <- ZtoNat_Zlength, SL; simpl; omega.
           destruct (zeq i 1); subst; simpl.
             rewrite upd_ilist_nth_diff; trivial.
             rewrite upd_ilist_nth_diff; trivial. omega. omega. omega.
             rewrite upd_intlist_Zlength, SL; simpl; try omega.
             rewrite upd_intlist_Zlength, SL; simpl; try omega.
             omega.
           assert (XX: (Z.to_nat (5 * 1) < length intsums)%nat).
               rewrite Z2Nat.inj_mul, <- ZtoNat_Zlength, SL; simpl; omega.
           destruct (zeq i 2); subst; simpl.
             rewrite upd_ilist_nth_diff; try omega.
             rewrite upd_ilist_nth_diff; try omega. 
             rewrite upd_ilist_nth_diff; try omega. 
             rewrite upd_ilist_nth_diff; trivial. omega. omega. omega.
             rewrite upd_intlist_Zlength, SL; simpl; try omega.
             rewrite upd_intlist_Zlength, SL; simpl; try omega.
             repeat rewrite upd_intlist_Zlength; simpl; try omega.
             repeat rewrite upd_intlist_Zlength; simpl; try omega.
             repeat rewrite upd_intlist_Zlength; simpl; try omega.
             repeat rewrite upd_intlist_Zlength; simpl; try omega.
           assert (YY: (Z.to_nat (6 + 1) < length intsums)%nat).
               rewrite Z2Nat.inj_add, <- ZtoNat_Zlength, SL; simpl; omega.
           destruct (zeq i 3); subst; simpl.
             rewrite upd_ilist_nth_diff; try omega.
             rewrite upd_ilist_nth_diff; try omega. 
             rewrite upd_ilist_nth_diff; try omega. 
             rewrite upd_ilist_nth_diff; try omega.
             rewrite upd_ilist_nth_diff; try omega. 
             rewrite upd_ilist_nth_diff; try omega. trivial.
             rewrite upd_intlist_Zlength, SL; simpl; try omega.
             rewrite upd_intlist_Zlength, SL; simpl; try omega.
             repeat rewrite upd_intlist_Zlength; simpl; try omega.
             repeat rewrite upd_intlist_Zlength; simpl; try omega.
             repeat rewrite upd_intlist_Zlength; simpl; try omega.
             repeat rewrite upd_intlist_Zlength; simpl; try omega.
             repeat rewrite upd_intlist_Zlength; simpl; try omega.
             repeat rewrite upd_intlist_Zlength; simpl; try omega.
             repeat rewrite upd_intlist_Zlength; simpl; try omega.
             repeat rewrite upd_intlist_Zlength; simpl; try omega. omega.
         + rewrite H0. apply upd_intlist_upd_reptype_array.
           assert (Znth (5 * i) intsums Int.zero = vj). 
           - clear - I Vj PL2length SL. unfold Znth in *.
             destruct (zlt (5 * i) 0); subst; simpl in *. omega.
             rewrite nth_map' with (d':=Int.zero) in Vj.
             Focus 2. rewrite PL2length. apply (Z2Nat.inj_lt _ 16); omega.
                      split; try omega. apply (Z2Nat.inj_lt _ 4); omega.
             inversion Vj; clear Vj. clear H0.
             destruct (zeq i 0); subst; simpl. trivial.
             assert (X: (Z.to_nat (5 * 0) < length intsums)%nat).
                 rewrite Z2Nat.inj_mul, <- ZtoNat_Zlength, SL; simpl; omega. 
             assert (Y: (Z.to_nat (6 + 0) < length intsums)%nat).
                 rewrite Z2Nat.inj_add, <- ZtoNat_Zlength, SL; simpl; omega. 
             destruct (zeq i 1); subst; simpl.
               rewrite upd_ilist_nth_diff; trivial.
               rewrite upd_ilist_nth_diff; trivial. omega. omega. omega.
               repeat rewrite upd_intlist_Zlength; simpl; try omega.
               repeat rewrite upd_intlist_Zlength; simpl; try omega. omega.
             assert (XX: (Z.to_nat (5 * 1) < length intsums)%nat).
                 rewrite Z2Nat.inj_mul, <- ZtoNat_Zlength, SL; simpl; omega.
             destruct (zeq i 2); subst; simpl.
               rewrite upd_ilist_nth_diff; try omega.
               rewrite upd_ilist_nth_diff; try omega. 
               rewrite upd_ilist_nth_diff; try omega. 
               rewrite upd_ilist_nth_diff; trivial. omega. omega. omega.
               repeat rewrite upd_intlist_Zlength; simpl; try omega.
               repeat rewrite upd_intlist_Zlength; simpl; try omega.
               repeat rewrite upd_intlist_Zlength; simpl; try omega.
               repeat rewrite upd_intlist_Zlength; simpl; try omega. 
               repeat rewrite upd_intlist_Zlength; simpl; try omega.
               repeat rewrite upd_intlist_Zlength; simpl; try omega. 
             assert (YY: (Z.to_nat (6 + 1) < length intsums)%nat).
                 rewrite Z2Nat.inj_add, <- ZtoNat_Zlength, SL; simpl; omega.
             destruct (zeq i 3); subst; simpl.
               rewrite upd_ilist_nth_diff; try omega.
               rewrite upd_ilist_nth_diff; try omega. 
               rewrite upd_ilist_nth_diff; try omega. 
               rewrite upd_ilist_nth_diff; try omega.
               rewrite upd_ilist_nth_diff; try omega. 
               rewrite upd_ilist_nth_diff; try omega. trivial.
               repeat rewrite upd_intlist_Zlength; simpl; try omega.
               repeat rewrite upd_intlist_Zlength; simpl; try omega.
               repeat rewrite upd_intlist_Zlength; simpl; try omega.
               repeat rewrite upd_intlist_Zlength; simpl; try omega. 
               repeat rewrite upd_intlist_Zlength; simpl; try omega.
               repeat rewrite upd_intlist_Zlength; simpl; try omega. 
               repeat rewrite upd_intlist_Zlength; simpl; try omega.
               repeat rewrite upd_intlist_Zlength; simpl; try omega.
               repeat rewrite upd_intlist_Zlength; simpl; try omega.
               repeat rewrite upd_intlist_Zlength; simpl; try omega. omega.
           - rewrite H1. apply upd_intlist_upd_reptype_array. trivial.
             rewrite PL2length. apply (Z2Nat.inj_lt _ 16); omega.
             split. omega. apply (Z2Nat.inj_lt _ 4); omega. 
           - rewrite upd_intlist_length, PL2length. apply (Z2Nat.inj_lt _ 16); omega.
             split. omega. apply (Z2Nat.inj_lt _ 4); omega. omega. 
             rewrite PL2length. apply (Z2Nat.inj_lt _ 16); omega.
             split. omega. apply (Z2Nat.inj_lt _ 4); omega. } 
       rewrite H0; reflexivity. }
entailer. 
Qed.


Definition UpdateOut (l: list val) (i:Z) (xi:int) :=
         (firstn (Z.to_nat i) l) ++ QuadByte2ValList (littleendian_invert xi) ++ skipn (Z.to_nat i+4) l.

Lemma UpdateOut_Zlength l i xi: 0<=i -> i + 4 <= Zlength l -> Zlength (UpdateOut l i xi) = Zlength l.
Proof. intros. unfold UpdateOut. repeat rewrite Zlength_app.
  rewrite <- QuadByteValList_ZLength, skipn_Zlength. 
  rewrite Zlength_correct, firstn_length, Min.min_l.
  rewrite Nat2Z.inj_add. rewrite <- (Z.add_comm (Z.of_nat 4)). Opaque Z.sub. simpl. 
  rewrite Z.add_sub_assoc. rewrite Zminus_plus_simpl_l. apply Zplus_minus.

  rewrite <- ZtoNat_Zlength. apply Z2Nat.inj_le; omega. 
  rewrite <- ZtoNat_Zlength. rewrite <- (Z2Nat.inj_add _ (Z.of_nat 4)); trivial.
  apply Z2Nat.inj_le; simpl; omega.
Qed. 

Lemma firstn_UpdateOut n k l x: (n <= length l)%nat ->  k=Z.of_nat n -> firstn n (UpdateOut l k x) = firstn n l.
Proof. intros; unfold UpdateOut; subst.
  rewrite firstn_app1, Nat2Z.id. apply coqlib3.firstn_firstn. omega.
  rewrite Nat2Z.id, firstn_length, Min.min_l; trivial.
Qed.

Lemma skipn_UpdateOut n k l x: (Z.to_nat k+4=n)%nat -> (Z.to_nat k <= length l)%nat -> skipn n (UpdateOut l k x) = skipn n l.
Proof. intros; unfold UpdateOut; subst.
  rewrite skipn_app2; rewrite firstn_length, Min.min_l; trivial. 2: omega. 
  rewrite skipn_app2; rewrite QuadByteValList_length, minus_plus. 2: omega.
  rewrite minus_diag. apply skipn_0.
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

Lemma HTrue_loop3 Espec: forall t y x w nonce out c k h OUT
  xs ys Nonce C K (ZL_X: Zlength xs = 16) (OL: Zlength OUT = 64),
@semax Espec 
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
Proof. intros.
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
    forward v.
    { entailer. rewrite Xi. entailer. }
    rewrite Xi.
    rewrite data_at_isptr with (p:=out). normalize.
    apply isptrD in H. destruct H as [ob [ooff OC]]. rewrite OC in *.
    forward v2. 
    rewrite <- P3_Zlength,
       (split3_offset_array_at tuchar (eq_refl _) ((4 * Z.to_nat i)%nat) 4 Tsh ll).
    Focus 2. simpl; rewrite P3_length.
             clear - I. destruct I. apply (plus_le_compat_r _ (60%nat) (4%nat)).
             apply (mult_le_compat_l _ 15 4). apply (Z2Nat.inj_le _ 15); omega.
    normalize.
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
    forward_call' (Vptr ob (Int.add ooff (Int.repr (4 * i))), xi).
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
    { entailer.
      rewrite Nat2Z.inj_mul, Z2Nat.id.
      apply (exp_right (firstn 4 (skipn (4 * Z.to_nat i) ll))).
      entailer.
      apply andp_right. 2: cancel.
      rewrite firstn_length, Min.min_l. apply prop_right. trivial.
          rewrite skipn_length, P3_length. apply inj_le'. rewrite Nat2Z.inj_sub, Nat2Z.inj_mul, Z2Nat.id. simpl. apply Z.le_add_le_sub_r. omega. omega.
          apply inj_le'. rewrite Nat2Z.inj_mul, Z2Nat.id. simpl. omega. omega.
      omega. }
    normalize. Opaque mult. 
    assert (Upd_ll_Zlength: Zlength (UpdateOut ll (4 * i) xi) = 64).
      rewrite UpdateOut_Zlength; trivial. omega. omega.
    assert (Upd_ll_length: length (UpdateOut ll (4 * i) xi) = 64%nat).
        rewrite <- ZtoNat_Zlength, Upd_ll_Zlength; reflexivity.

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
    { clear Heqll. entailer. cancel. unfold QByte.
      rewrite <- Upd_ll_Zlength.
      specialize (append_split3_Tarray_at tuchar
          (firstn (4 * Z.to_nat i) ll) 
          (QuadByte2ValList (littleendian_invert _id0))
          (skipn (4 * Z.to_nat i + 4) ll)
          (UpdateOut ll (4 * i) _id0)
          Tsh (eq_refl _)). unfold tarray; intros AS.
      rewrite AS; clear AS. entailer.
      apply andp_right. apply prop_right. simpl; rewrite Upd_ll_Zlength. simpl in *. rewrite P3_Zlength in H0. apply H0.
      assert (ZL1: (Zlength (firstn (4 * Z.to_nat i) ll) = 4*i)%Z).
        rewrite Zlength_correct, firstn_length, Min.min_l, Nat2Z.inj_mul, Z2Nat.id. reflexivity. omega.
        rewrite P3_length. apply Nat2Z.inj_le. rewrite Nat2Z.inj_mul, Z2Nat.id. simpl; omega. omega.
      Opaque Z.mul.
      rewrite <- QuadByteValList_ZLength.
      apply sepcon_derives. simpl; rewrite ZL1; cancel.
      rewrite skipn_Zlength. simpl; rewrite ZL1. rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id. cancel. omega.
      rewrite P3_length. apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id. simpl; omega. omega.
      unfold UpdateOut. rewrite Z2Nat.inj_mul. reflexivity. omega. omega. }
 
    destruct (Znth_mapVint xs (6+i) Vundef) as [zi Zi]. omega.
    forward u.
    { entailer. rewrite Zi. entailer. }
    rewrite Zi.
    forward u2. 
    rewrite <- Upd_ll_Zlength.
    rewrite (split3_offset_array_at tuchar (eq_refl _) ((16 + 4 * Z.to_nat i)%nat) 4 Tsh (UpdateOut ll (4 * i) xi)).
    Focus 2. Opaque plus. simpl. rewrite Upd_ll_length.
             clear - I. destruct I. rewrite <- plus_assoc. apply (plus_le_compat_l _ (48%nat) (16%nat)).
             apply (plus_le_compat_r _ (44%nat) (4%nat)).
             apply (mult_le_compat_l _ 11 4). apply (Z2Nat.inj_le _ 11); omega.
    normalize.
    assert (ArithA: (16 + 4 * Z.to_nat i + 4 <= 64)%nat).
      apply inj_le'. repeat rewrite Nat2Z.inj_add. rewrite Nat2Z.inj_mul, Z2Nat.id. simpl. omega. omega.
    assert (ArithB: (16 + 4 * Z.to_nat i <= 64)%nat).
      apply inj_le'. rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id. simpl. omega. omega.
         
Transparent core_spec. Transparent ld32_spec. Transparent L32_spec. Transparent st32_spec.
Transparent crypto_core_salsa20_spec. Transparent crypto_core_hsalsa20_spec.
    forward_call' (Vptr ob (Int.add ooff (Int.repr (16 + 4 * i))), zi).
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.
    { entailer.
      rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id. 2: omega.
      apply (exp_right (firstn 4 (skipn (16 + 4 * Z.to_nat i) (UpdateOut ll (4 * i) xi)))).
      entailer.
      apply andp_right. 2: cancel.
      rewrite firstn_length, Min.min_l; try omega. apply prop_right; trivial.
          rewrite skipn_length, Upd_ll_length. 
          apply inj_le'. rewrite Nat2Z.inj_sub, Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id. simpl. apply Z.le_add_le_sub_r. omega. omega.
          apply inj_le'. rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id. simpl. omega. omega. }
    normalize. entailer. cancel.
    assert (AA:  Z.to_nat (i + 1) = S (Z.to_nat i)).
      rewrite (Z.add_comm _ 1), Z2Nat.inj_add. simpl. apply NPeano.Nat.add_1_l. omega. omega.
    rewrite AA. simpl. 
    clear H5 H6 H7 H8 TC0 H9 H11 H12 H13 H14 H10 TC TC1 TC2 TC3.
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
    assert (LU_length: length (UpdateOut l (16+4 * i) _id0) = 64%nat).
        rewrite <- ZtoNat_Zlength, ZLU; reflexivity.
    rewrite <- ZLU.
      specialize (append_split3_Tarray_at tuchar
          (firstn (16 + 4 * Z.to_nat i) (UpdateOut l (16 + 4 * i) _id0)) 
          (QuadByte2ValList (littleendian_invert _id0))
          (skipn (16 + 4 * Z.to_nat i + 4) (UpdateOut l (16 + 4 * i) _id0))
          (UpdateOut l (16 + 4 * i) _id0)
          Tsh (eq_refl _)). unfold tarray; intros AS.
      rewrite AS; clear AS. entailer.
      apply andp_right. apply prop_right. simpl; rewrite ZLU. simpl in *. rewrite P3_Zlength in H0. apply H0.
      rewrite firstn_Zlength, skipn_Zlength.
      2: rewrite LU_length; trivial. 
      2: rewrite LU_length; trivial. 
      rewrite <- QuadByteValList_ZLength. repeat rewrite Nat2Z.inj_add. repeat rewrite Nat2Z.inj_mul.
      repeat rewrite Z2Nat.id; try omega.
      rewrite (firstn_UpdateOut _ (16 + 4 * i)), ZLU, Upd_ll_Zlength, (skipn_UpdateOut _ (16 + 4 * i)). cancel.
      rewrite Z2Nat.inj_add, Z2Nat.inj_mul; try omega. reflexivity.
      rewrite <- ZtoNat_Zlength, Upd_ll_Zlength. apply Z2Nat.inj_le; omega. 
      rewrite Upd_ll_length; assumption.
      rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id; simpl; omega.

      unfold UpdateOut. rewrite Z2Nat.inj_add, Z2Nat.inj_mul; try omega.
      assert (LL1: (length (firstn (Z.to_nat 16 + Z.to_nat 4 * Z.to_nat i) l) = 16+4*Z.to_nat i)%nat).
         rewrite firstn_length, Min.min_l. simpl; omega. 
         rewrite Upd_ll_length. assumption. 
      assert (AR1: (16 + 4 * Z.to_nat i <=
              length (firstn (Z.to_nat 16 + Z.to_nat 4 * Z.to_nat i) l))%nat).
        rewrite LL1. omega.
      f_equal. rewrite firstn_app1; trivial. 
          specialize (@firstn_firstn val (16 + 4 * Z.to_nat i) 0). rewrite plus_0_r; intros.
          apply H1.
      f_equal. rewrite skipn_app2; rewrite LL1. 2: omega.
        rewrite minus_plus.
        rewrite skipn_app2; rewrite QuadByteValList_length.
          rewrite minus_diag; apply skipn_0. omega. }
entailer. (*With temp _i (Vint (Int.repr 4)) in LOCAL of HTruePostCondL apply derives_refl.*)
Qed.

Lemma hposLoop2_Zlength16 C N l (L:Zlength l = 16): forall n, 
      5 * Z.of_nat n < 16-> 6+ Z.of_nat n < 16 -> Zlength (hPosLoop2 (S n) l C N) = 16.
Proof. intros. simpl. 
  induction n; simpl; intros; trivial.
  rewrite upd_intlist_Zlength; rewrite upd_intlist_Zlength; omega. 
  rewrite Nat2Z.inj_succ in *.
  rewrite upd_intlist_Zlength; rewrite upd_intlist_Zlength; rewrite IHn; simpl; try omega. 
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

Lemma verif_fcore_epilogue_htrue Espec: forall t y x w nonce out c k h OUT
  xs ys Nonce C K (ZL_X: Zlength xs = 16) (ZL_Y: Zlength ys = 16) (L_OUT: Zlength OUT = 64),
@semax Espec
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
                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                       (Etempvar _i tint) (tptr tuint)) tuint))
              (Sassign
                 (Ederef
                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                       (Etempvar _i tint) (tptr tuint)) tuint)
                 (Ebinop Oadd (Etempvar _aux tuint) (Etempvar _aux1 tuint)
                    tuint))))
        (Sset _i
           (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint)))
     (Ssequence
        (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
           (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 4) tint) tint)
           (Ssequence
              (Sset _u8_aux
                 (Ebinop Oadd (Etempvar _c (tptr tuchar))
                    (Ebinop Omul (Econst_int (Int.repr 4) tint)
                       (Etempvar _i tint) tint) (tptr tuchar)))
              (Ssequence
                 (Ssequence
                    (Scall (Some _aux'8)
                       (Evar _ld32
                          (Tfunction (Tcons (tptr tuchar) Tnil) tuint
                             cc_default)) [Etempvar _u8_aux (tptr tuchar)])
                    (Sset _aux (Etempvar _aux'8 tuint)))
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
                                (Scall (Some _aux'9)
                                   (Evar _ld32
                                      (Tfunction (Tcons (tptr tuchar) Tnil)
                                         tuint cc_default))
                                   [Etempvar _u8_aux (tptr tuchar)])
                                (Sset _aux (Etempvar _aux'9 tuint)))
                             (Ssequence
                                (Sset _aux1
                                   (Ederef
                                      (Ebinop Oadd
                                         (Evar _x (tarray tuint 16))
                                         (Ebinop Oadd
                                            (Econst_int (Int.repr 6) tint)
                                            (Etempvar _i tint) tint)
                                         (tptr tuint)) tuint))
                                (Sassign
                                   (Ederef
                                      (Ebinop Oadd
                                         (Evar _x (tarray tuint 16))
                                         (Ebinop Oadd
                                            (Econst_int (Int.repr 6) tint)
                                            (Etempvar _i tint) tint)
                                         (tptr tuint)) tuint)
                                   (Ebinop Osub (Etempvar _aux1 tuint)
                                      (Etempvar _aux tuint) tuint)))))))))
           (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                 tint)))
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
                          (Tfunction (Tcons (tptr tuchar) (Tcons tuint Tnil))
                             tvoid cc_default))
                       [Etempvar _u8_aux (tptr tuchar); Etempvar _aux tuint])
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
                             (Evar _st32
                                (Tfunction
                                   (Tcons (tptr tuchar) (Tcons tuint Tnil))
                                   tvoid cc_default))
                             [Etempvar _u8_aux (tptr tuchar);
                             Etempvar _aux tuint]))))))
           (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                 tint)))))
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
           rewrite hposLoop2_Zlength16; trivial.
  entailer. 
unfold POSTCONDITION, abbreviate, HTruePostCond. Opaque ThirtyTwoByte. Opaque hPosLoop2. Opaque hPosLoop3.
intros. entailer. simpl. apply normal_ret_assert_derives.
apply (exp_right intsums). entailer.
apply prop_right. clear - HSums1 SL. intros.
  destruct (HSums1 _ H) as [xj [Xj [X _]]].
  destruct X as [yj [Yi Sj]]. apply H.
  exists xj, yj. auto.
Qed.