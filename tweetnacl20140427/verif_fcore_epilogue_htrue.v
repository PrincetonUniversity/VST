Require Import VST.floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import sha.general_lemmas.

Require Import tweetnacl20140427.split_array_lemmas.
Require Import ZArith.
Require Import tweetnacl20140427.tweetNaclBase.
Require Import tweetnacl20140427.Salsa20.
Require Import tweetnacl20140427.tweetnaclVerifiableC.
Require Import tweetnacl20140427.verif_salsa_base.

Require Import tweetnacl20140427.spec_salsa.
Opaque Snuffle.Snuffle. Opaque prepare_data.

(*TODO: eliminate*)
Ltac canon_load_result ::= idtac.

Definition HTrue_inv1 l i ys xs : Prop :=
      Zlength l = 16 /\ exists ints, l=map Vint ints /\
               forall j, 0<=j<16 -> exists xj,
                Znth j xs = Vint xj
                /\ (j<i -> exists yj, Znth j ys = Vint yj /\
                                      Znth j l = Vint (Int.add yj xj))
                /\ (i<=j ->  Znth j l = Vint xj).

Definition htrue_loop1_statement:=
Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 16) tint) tint)
     (Ssequence
        (Sset _t'17
           (Ederef
              (Ebinop Oadd (Evar _x (tarray tuint 16)) (Etempvar _i tint)
                 (tptr tuint)) tuint))
        (Ssequence
           (Sset _t'18
              (Ederef
                 (Ebinop Oadd (Evar _y (tarray tuint 16)) (Etempvar _i tint)
                    (tptr tuint)) tuint))
           (Sassign
              (Ederef
                 (Ebinop Oadd (Evar _x (tarray tuint 16)) (Etempvar _i tint)
                    (tptr tuint)) tuint)
              (Ebinop Oadd (Etempvar _t'17 tuint) (Etempvar _t'18 tuint)
                 tuint))))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)).

Lemma HTrue_loop1 Espec (FR:mpred) t y x w nonce out c k h (xs ys: list int):
@semax CompSpecs Espec
  (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs nil)
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 20)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 16) (map Vint ys) y;
         data_at Tsh (tarray tuint 16) (map Vint xs) x))
 htrue_loop1_statement
 (normal_ret_assert
    (PROP  ()
     LOCAL  (temp _i (Vint (Int.repr 16)); lvar _t (tarray tuint 4) t;
             lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
             lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out;
             temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
     SEP (FR; data_at Tsh (tarray tuint 16) (map Vint ys) y;
          EX  l : list val, !!HTrue_inv1 l 16 (map Vint ys) (map Vint xs) &&
               data_at Tsh (tarray tuint 16) l x))).
Proof.
  abbreviate_semax.
  Time assert_PROP (Zlength (map Vint xs) = 16 /\ Zlength (map Vint ys) = 16)
     as XLYL by entailer!. (*2 versus 2.6*)
  destruct XLYL as [XL YL].
  unfold htrue_loop1_statement.
  Time forward_for_simple_bound 16 (EX i:Z,
   (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 16) (map Vint ys) y;
         EX l:_, !!HTrue_inv1 l i (map Vint ys) (map Vint xs)
              && data_at Tsh (tarray tuint 16) l x))). (*1.2 versus 3.3*)
  { Exists (map Vint xs).
    Time entailer!. (*3.3 versus 3.9*)
    split. assumption.
    exists xs; split; trivial.
    intros.
    destruct (Znth_mapVint xs j) as [xj Xj]. rewrite Zlength_map in XL; omega.
    exists xj; split; trivial.
    split; intros. omega. trivial. }
  { rename H into I. Intros xlist.
    destruct H as [XLL XLIST].
    destruct XLIST as [xints [INTS J]]. subst xlist.
    destruct (J _ I) as [xi [Xi [_ HXi]]].
    destruct (Znth_mapVint ys i) as [yi Yi]. rewrite Zlength_map in YL; omega.
    freeze [0;1] FR1.
    spec HXi; [omega|]. change Inhabitant_val with Vundef in HXi.
    Time forward; rewrite HXi.
    thaw FR1. freeze [0;2] FR2.
    Time forward; change Inhabitant_val with Vundef in Yi; rewrite Yi. 
    thaw FR2.
    Time forward. (*4.8 versus 7.4*)
    Exists (upd_Znth i (map Vint xints) (Vint (Int.add yi xi))).
    go_lower. normalize. 
    apply andp_right; [ apply prop_right | rewrite Int.add_commut; cancel].
    repeat split; trivial; try omega. 
    * rewrite upd_Znth_Zlength. assumption. simpl; rewrite XLL. omega.
    * eexists; split. apply upd_Znth_ints.
      intros kk KK. destruct (J _ KK) as [xj [Xj [IJ1 IJ2]]].
      exists xj. split. assumption.
      split; intros.
      + destruct (zlt kk i).
        - destruct (IJ1 l) as [yj [Yj Xj']]. exists yj; split; trivial.
          rewrite upd_Znth_diff; trivial.
            simpl in *; omega.
            simpl in *; omega.
            omega.
        - assert (JJ: kk=i) by omega. subst kk.
          rewrite Xj in Xi; inv Xi.
          rewrite @upd_Znth_same.
          exists yi. change Inhabitant_val with Vundef; split; trivial.
          simpl in *; omega.
      + rewrite upd_Znth_diff. apply IJ2; omega.
            simpl in *; omega.
            simpl in *; omega.
            omega. }
apply andp_left2; apply derives_refl.
Time Qed. (*June 4th, 2017 (loptop): 1.4s*)

(* Fragment:
       FOR(i,4) {
        x[5*i] -= ld32(c+4*i);
        x[6+i] -= ld32(in+4*i);
       }*)
Definition HTrue_loop2_statement :=
Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 4) tint) tint)
     (Ssequence
        (Ssequence
           (Scall (Some _t'9)
              (Evar _ld32
                 (Tfunction (Tcons (tptr tuchar) Tnil) tuint cc_default))
              [Ebinop Oadd (Etempvar _c (tptr tuchar))
                 (Ebinop Omul (Econst_int (Int.repr 4) tint)
                    (Etempvar _i tint) tint) (tptr tuchar)])
           (Ssequence
              (Sset _t'16
                 (Ederef
                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                       (Ebinop Omul (Econst_int (Int.repr 5) tint)
                          (Etempvar _i tint) tint) (tptr tuint)) tuint))
              (Sassign
                 (Ederef
                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                       (Ebinop Omul (Econst_int (Int.repr 5) tint)
                          (Etempvar _i tint) tint) (tptr tuint)) tuint)
                 (Ebinop Osub (Etempvar _t'16 tuint) (Etempvar _t'9 tuint)
                    tuint))))
        (Ssequence
           (Scall (Some _t'10)
              (Evar _ld32
                 (Tfunction (Tcons (tptr tuchar) Tnil) tuint cc_default))
              [Ebinop Oadd (Etempvar _in (tptr tuchar))
                 (Ebinop Omul (Econst_int (Int.repr 4) tint)
                    (Etempvar _i tint) tint) (tptr tuchar)])
           (Ssequence
              (Sset _t'15
                 (Ederef
                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                       (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                          (Etempvar _i tint) tint) (tptr tuint)) tuint))
              (Sassign
                 (Ederef
                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                       (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                          (Etempvar _i tint) tint) (tptr tuint)) tuint)
                 (Ebinop Osub (Etempvar _t'15 tuint) (Etempvar _t'10 tuint)
                    tuint)))))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)).

Fixpoint hPosLoop2 (n:nat) (sumlist: list int) (C Nonce: SixteenByte): list int :=
       match n with
         O => sumlist
       | S m => let j:= Z.of_nat m in
                let s := hPosLoop2 m sumlist C Nonce in
                let five := Int.sub (Znth (5*j) sumlist) (littleendian (Select16Q C j)) in
                let six := Int.sub (Znth (6+j) sumlist) (littleendian (Select16Q Nonce j)) in
                upd_Znth (6+j) (upd_Znth (5*j) s five) six
       end.

Lemma HTrue_loop2 Espec (FR:mpred) t y x w nonce out c k h intsums Nonce C K:
@semax CompSpecs Espec
  (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs nil)
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t;
     lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
     lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
     temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; CoreInSEP(Nonce, C, K) (nonce, c, k);
         data_at Tsh (tarray tuint 16) (map Vint intsums) x))
  HTrue_loop2_statement
 (normal_ret_assert (PROP  ()
 LOCAL  (temp _i (Vint (Int.repr 4)); lvar _t (tarray tuint 4) t;
         lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
         lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
         temp _k k; temp _h (Vint (Int.repr h)))
 SEP  (FR; CoreInSEP(Nonce, C, K) (nonce, c, k);
        data_at Tsh (tarray tuint 16) (map Vint (hPosLoop2 4 intsums C Nonce)) x))).
Proof. intros. abbreviate_semax.
  freeze [0;1] FR1.
  Time assert_PROP (Zlength (map Vint intsums) = 16) as SL by entailer!. (*0.9 versus 2.7*)
  rewrite Zlength_map in SL.
  thaw FR1.
  unfold HTrue_loop2_statement.
  Time forward_for_simple_bound 4 (EX i:Z,
  (PROP  ()
   LOCAL  ((*NOTE: we have to remove the old i here to get things to work: temp _i (Vint (Int.repr 16)); *)
           lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; CoreInSEP (Nonce, C, K) (nonce, c, k);
   data_at Tsh (tarray tuint 16) (map Vint (hPosLoop2 (Z.to_nat i) intsums C Nonce)) x))). (*2.7 versus 3.2*)
   Time solve[entailer!]. (*1.6 versus 4.4*)
   { rename H into I.
      unfold CoreInSEP. do 2 flatten_sepcon_in_SEP.
      freeze [0;3] FRk.
      unfold SByte at 2.
      Time assert_PROP (isptr c) as Pc by entailer!. (*3.2 versus 4.1*)
      apply isptrD in Pc; destruct Pc as [cb [coff HC]]. rewrite HC in *.
     assert (C16:= SixteenByte2ValList_Zlength C).
      remember (SplitSelect16Q C i) as FB; destruct FB as (Front, BACK).
      specialize (Select_SplitSelect16Q C i _ _ HeqFB); intros SSS.
      Time assert_PROP (field_compatible (Tarray tuchar 16 noattr) [] (Vptr cb coff))
        as FC by entailer!. (*1.8 versus 4.3*)
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
    flatten_sepcon_in_SEP.
    freeze [0;1;3] FR2.
    freeze [0;2] FR3. 
    Time forward_call ((Vptr cb (Ptrofs.add coff (Ptrofs.repr (4 * i)))),
                      Select16Q C i). (*2.4 versus 10.3*)
      assert (PL2length: forall n, (0<=n<4)%nat -> Zlength (hPosLoop2 n intsums C Nonce) = 16).
        clear - SL.
        induction n; simpl; intros. trivial.
        repeat rewrite upd_Znth_Zlength. apply IHn; omega. omega.
          rewrite IHn; omega.
          rewrite IHn; omega.
      assert (PL2Zlength: Zlength (hPosLoop2 (Z.to_nat i) intsums C Nonce) = 16).
         apply PL2length. split; try omega. apply (Z2Nat.inj_lt _ 4); omega.

      destruct (Znth_mapVint (hPosLoop2 (Z.to_nat i) intsums C Nonce) (5*i)) as [vj Vj].
      rewrite PL2Zlength; omega.
      thaw FR3.
      Time forward; change (@Znth val Vundef) with (@Znth val Inhabitant_val); rewrite Vj. (*5.3 versus 10.9*) 
      Time forward. (*4.9 versus 10.3*)

      thaw FR2. freeze [0;1;3;4] FR3.
      unfold SByte.
      Time assert_PROP (isptr nonce /\ field_compatible (Tarray tuchar 16 noattr) [] nonce)
        as PnonceFCN by entailer!. (*1.8 versus 4.9*)
      destruct PnonceFCN as [Pnonce FCN].
      apply isptrD in Pnonce; destruct Pnonce as [nb [noff NC]]; rewrite NC in *.

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
      flatten_sepcon_in_SEP.

      freeze [0;2] FR4.
      Time forward_call (Vptr nb (Ptrofs.add noff (Ptrofs.repr (4 * i))),
                     Select16Q Nonce i). (*3 versus 14.8*)
     destruct (Znth_mapVint (hPosLoop2 (Z.to_nat i) intsums C Nonce) (6+i)) as [uj Uj].
      rewrite PL2Zlength; omega.
     thaw FR4. thaw FR3. freeze [0;1;2;3;5] FR5.
     autorewrite with sublist in *.
     Time forward; rewrite upd_Znth_diff; try (rewrite Zlength_map, PL2Zlength; simpl; omega). (*5.9 versus 13*)
     { Time entailer!. (*2 versus 4.6*)
(*       destruct (Zlength_length _ Front (Zlength Front)) as [X _]. omega.
       rewrite X; trivial. autorewrite with sublist; simpl; trivial. *) }
     { omega. }
     2: omega.
     Opaque Z.mul. Opaque Z.add.
     Time forward. (*5.8 versus 12.9*)
     autorewrite with sublist; rewrite Uj.
     Transparent Z.add. Transparent Z.mul.
    entailer!.
(*Issue: substitution in entailer/entailer! is a bit too eager here. Without the following assert (FLN: ...) ... destruct FLN,
  the two hypotheses are simply combined to Zlength Front = Zlength FrontN by entailer (and again by the inv H0) *)
     assert (FLN: Zlength Front = i /\ Zlength FrontN = i). split; assumption. clear FL FN.
     Time entailer!. (*4.8 versus 11.6*)
     destruct FLN as [FL FN].
     thaw FR5. thaw FRk. Time cancel. (*2.2*)
(*     rewrite Znth_map with (d':=Int.zero) by rep_omega.
     rewrite Uj.
*)
     entailer!.
     (*rewrite Uj. simpl.*)
     repeat rewrite <- sepcon_assoc.
     apply sepcon_derives.
     + unfold SByte, QByte. (*subst c nonce.*)
       erewrite (Select_Unselect_Tarray_at 16); try reflexivity; try assumption.
       2: rewrite NNN; reflexivity.
       erewrite (Select_Unselect_Tarray_at 16); try reflexivity; try assumption.
       2: rewrite SSS; reflexivity.
       unfold Select_at. repeat rewrite QuadChunk2ValList_ZLength. (*rewrite FL, FLN. *)
       rewrite Zmult_1_r. simpl.
        repeat rewrite app_nil_r. rewrite FN; cancel.       
       rewrite <- SSS, <- C16; trivial.
       rewrite <- SSS, <- C16. cbv; trivial.
       rewrite <- NNN, <- N16; trivial.
       rewrite <- NNN, <- N16. cbv; trivial.
     + Time normalize. apply isptrD in Px. destruct Px as [xb [xoff XP]]; subst x.
       apply data_at_ext.
       clear H1.
       remember (Zlength Front) as i.
       rewrite (Zplus_comm i 1), Z2Nat.inj_add; simpl; try omega.
       replace (length Front) with (Z.to_nat i).
       rewrite Z2Nat.id by omega.
       rewrite upd_Znth_ints.
       autorewrite with sublist.
       f_equal.
       unfold upd_Znth.
       assert (VJeq: Znth (5 * i) (hPosLoop2 (Z.to_nat i) intsums C Nonce) =
                Znth (5 * i) intsums). {
         clear - SL PL2length I.
         destruct (zeq i 0); subst; simpl; [ trivial | ].
         destruct (zeq i 1); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega. trivial.
         destruct (zeq i 2); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega. trivial.
         destruct (zeq i 3); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega. trivial.
         omega. }
      assert (EQ: Znth (6 + i) (hPosLoop2 (Z.to_nat i) intsums C Nonce) =
                   Znth (6 + i) intsums).  {
         clear - SL PL2length I.
         destruct (zeq i 0); subst; simpl. trivial.
         destruct (zeq i 1); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega. trivial.
         destruct (zeq i 2); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega. trivial.
         destruct (zeq i 3); subst; simpl.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega.
               rewrite upd_Znth_diff; repeat rewrite upd_Znth_Zlength; try omega. trivial.
         omega. }
(*        rewrite Znth_map with (d':=Int.zero) by rep_omega. *)
        rewrite !VJeq, !EQ.
        simpl force_val.
        autorewrite with sublist.
        rewrite !sublist_map.
        rewrite map_app. reflexivity.
        subst i. rewrite Zlength_correct. rewrite Nat2Z.id. auto.
   }
  apply andp_left2; apply derives_refl.
Time Qed. (*June 4th, 2017 (laptop: Finished transaction in 4.418 secs (3.784u,0.004s) (successful)*)

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
                let five := Znth (5*j) xlist in
                let six := Znth (6+j) xlist in
                UpdateOut (UpdateOut s (4*j) five) (16+4*j) six
       end.

     Opaque Z.mul. Opaque Z.add.

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
Lemma hposLoop2_Zlength16 C N l (L:Zlength l = 16): forall n,
      5 * Z.of_nat n < 16-> 6+ Z.of_nat n < 16 -> Zlength (hPosLoop2 (S n) l C N) = 16.
Proof. intros. simpl.
  induction n; simpl; intros; trivial.
  rewrite upd_Znth_Zlength; rewrite upd_Znth_Zlength; omega.
  rewrite Nat2Z.inj_succ in *.
  rewrite upd_Znth_Zlength; rewrite upd_Znth_Zlength; rewrite IHn; simpl; try omega.
  rewrite Zpos_P_of_succ_nat. omega.
  rewrite Zpos_P_of_succ_nat. omega.
  rewrite Zpos_P_of_succ_nat. omega.
Qed.


     Transparent Z.add. Transparent Z.mul.

Definition HTrue_loop3_statement :=
Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 4) tint) tint)
     (Ssequence
        (Ssequence
           (Sset _t'14
              (Ederef
                 (Ebinop Oadd (Evar _x (tarray tuint 16))
                    (Ebinop Omul (Econst_int (Int.repr 5) tint)
                       (Etempvar _i tint) tint) (tptr tuint)) tuint))
           (Scall None
              (Evar _st32
                 (Tfunction (Tcons (tptr tuchar) (Tcons tuint Tnil)) tvoid
                    cc_default))
              [Ebinop Oadd (Etempvar _out (tptr tuchar))
                 (Ebinop Omul (Econst_int (Int.repr 4) tint)
                    (Etempvar _i tint) tint) (tptr tuchar);
              Etempvar _t'14 tuint]))
        (Ssequence
           (Sset _t'13
              (Ederef
                 (Ebinop Oadd (Evar _x (tarray tuint 16))
                    (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                       (Etempvar _i tint) tint) (tptr tuint)) tuint))
           (Scall None
              (Evar _st32
                 (Tfunction (Tcons (tptr tuchar) (Tcons tuint Tnil)) tvoid
                    cc_default))
              [Ebinop Oadd
                 (Ebinop Oadd (Etempvar _out (tptr tuchar))
                    (Econst_int (Int.repr 16) tint) (tptr tuchar))
                 (Ebinop Omul (Econst_int (Int.repr 4) tint)
                    (Etempvar _i tint) tint) (tptr tuchar);
              Etempvar _t'13 tuint])))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)).

Lemma HTrue_loop3 Espec (FR:mpred) t y x w nonce out c k h (OUT: list val) xs (*ys Nonce C K*):
@semax CompSpecs Espec
  (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs nil)
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuchar 32) OUT out;
         data_at Tsh (tarray tuint 16) (map Vint xs) x))
HTrue_loop3_statement
(normal_ret_assert (
  PROP  ()
  LOCAL  (lvar _t (tarray tuint 4) t;
          lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
          lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
          temp _k k; temp _h (Vint (Int.repr h)))
  SEP (FR; data_at Tsh (tarray tuint 16) (map Vint xs) x;
       data_at Tsh (tarray tuchar 32) (hPosLoop3 4 xs OUT) out))).
Proof. intros. abbreviate_semax.
 Time assert_PROP (Zlength (map Vint xs) = 16 /\ Zlength OUT = 32) as XX by entailer!. (*1.6 versus 3.5*)
 rewrite Zlength_map in XX. destruct XX as [ZL_X OL].
 unfold HTrue_loop3_statement.
 Time forward_for_simple_bound 4 (EX i:Z,
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuint 16) (map Vint xs) x;
         data_at Tsh (tarray tuchar 32) (hPosLoop3 (Z.to_nat i) xs OUT) out))). (*1.6 versus 3.4*)
    Time entailer!. (*2 versus 6*)
  { rename H into I.

    assert (P3_Zlength: Zlength (hPosLoop3 (Z.to_nat i) xs OUT) = 32).
      rewrite hposLoop3_length. assumption. rewrite OL, Z2Nat.id; omega.
    assert (P3_length: length (hPosLoop3 (Z.to_nat i) xs OUT) = 32%nat).
      rewrite <- ZtoNat_Zlength, P3_Zlength; reflexivity.
    remember (hPosLoop3 (Z.to_nat i) xs OUT) as ll. (*clear Heqll.*)

    destruct (Znth_mapVint xs (5 * i)) as [xi Xi]. omega.
    freeze [0;2] FR1.
    Time forward; change (@Znth val Vundef) with (@Znth val Inhabitant_val); rewrite Xi. (*3.7 versus 8.8*)
    thaw FR1.
    freeze [0;2] FR2.
    Time assert_PROP (isptr out /\ field_compatible (Tarray tuchar 32 noattr) [] out)
          as Pout_FCO by entailer!. (*1.2 versus 3.6*)
    destruct Pout_FCO as [Pout FCO].
    apply isptrD in Pout; destruct Pout as [ob [ooff OC]]; rewrite OC in *.
    rewrite <- P3_Zlength.
    rewrite (split3_data_at_Tarray_tuchar Tsh (Zlength ll) (4 *i) (4+4*i)); try rewrite P3_Zlength; trivial; try omega.
    rewrite field_address0_offset by auto with field_compatible.
    rewrite field_address0_offset by auto with field_compatible.
    unfold offset_val; simpl.
    repeat flatten_sepcon_in_SEP.
    freeze [0;1;3] FR3.
    rewrite Znth_map in Xi; try omega. 
    inversion Xi; clear Xi; subst xi.
    Time forward_call (offset_val (4 * i) (Vptr ob ooff), (Znth (5 * i) xs)).
    1: solve [autorewrite with sublist; entailer!]. 
    simpl.
    assert (Upd_ll_Zlength: Zlength (UpdateOut ll (4 * i) (Znth (5 * i) xs)) = 32).
      rewrite UpdateOut_Zlength; trivial; omega.
deadvars!.
    apply semax_pre with (P':=
  (PROP  ()
   LOCAL  ((*temp _u8_aux (Vptr ob (Int.add ooff (Int.repr (4 * i))));
   temp _aux (Vint (Znth (5 * i) xs Int.zero));*) temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out (Vptr ob ooff); temp _c c; temp _k k;
   temp _h (Vint (Int.repr h)))
   SEP 
   (FR; data_at Tsh (tarray tuchar 32) (UpdateOut ll (4*i) (Znth (5 * i) xs)) (Vptr ob ooff);
   data_at Tsh (tarray tuint 16) (map Vint xs) x))).
    { clear Heqll. Time entailer!. (*2.5 versus 7.5*)
      thaw FR3. thaw FR2. cancel.
      unfold QByte.
      rewrite <- Upd_ll_Zlength. unfold tarray. 
      erewrite (split3_data_at_Tarray_tuchar Tsh _ (4 * i) (4+4 * i) (UpdateOut ll (4 * i) (Znth (5 * i) xs)));
       try rewrite UpdateOut_Zlength, P3_Zlength; try omega.
      rewrite field_address0_offset by auto with field_compatible.
      rewrite field_address0_offset by auto with field_compatible.
      unfold offset_val. Opaque QuadByte2ValList.  simpl. repeat rewrite Z.mul_1_l.
      unfold UpdateOut.
      autorewrite with sublist. Time cancel. (*0.5*)
      rewrite sublist_app2; autorewrite with sublist; try omega.
      rewrite sublist_app2; try rewrite <- QuadByteValList_ZLength; try omega.
      autorewrite with sublist. rewrite Zplus_comm.
      apply derives_refl'. f_equal. f_equal. omega. }

    destruct (Znth_mapVint xs (6+i)) as [zi Zi]. omega.
    freeze [0;1] FR4.
    Time forward;  change (@Znth val Vundef) with (@Znth val Inhabitant_val);  rewrite Zi. (*5 versus 11.1*)
    thaw FR4. freeze [0;2] FR5.
    erewrite (split3_data_at_Tarray_tuchar Tsh 32 (16 + 4 *i) (4+16 + 4 *i)); trivial; try omega.
    rewrite field_address0_offset by auto with field_compatible.
    rewrite field_address0_offset by auto with field_compatible.
    unfold offset_val; simpl.
    autorewrite with sublist. repeat rewrite Z.mul_1_l.
    repeat flatten_sepcon_in_SEP.

    freeze [0;1;3] FR6.
    Time forward_call (Vptr ob (Ptrofs.add ooff (Ptrofs.repr (16 + 4 * i))), zi). (*3.1 versus 11.2*)
(*    { entailer!. (*Exists (sublist (16 + 4 * i) (4 + (16 + 4 * i)) (UpdateOut ll (4 * i) (Znth (5 * i) xs Int.zero))).*)
      autorewrite with sublist. rewrite Z.add_assoc. 
      Time entailer!. (*1.2 versus 13.5*) }*)

    Time entailer!. (*3.6 versus 11.5*)
    assert (AA:  Z.to_nat (i + 1) = S (Z.to_nat i)).
      rewrite (Z.add_comm _ 1), Z2Nat.inj_add. simpl. apply NPeano.Nat.add_1_l. omega. omega.
    rewrite AA. simpl.
    thaw FR6. thaw FR5. Time cancel. (*0.8*)
(*    rewrite <- Heqll. clear Heqll.*)
(*    remember (hPosLoop3 (Z.to_nat i) xs OUT) as ll; clear Heqll.*)
    (*assert (XXi: xi = Znth (5 * i) xs Int.zero).
      rewrite Znth_map' with (d':=Int.zero) in Xi; try omega. clear -Xi. inv Xi. trivial.*)
    assert (ZZi: zi = Znth (6 + i) xs).
    clear -Zi. inv Zi. trivial.
    rewrite Z2Nat.id, (*<- XXi,*) <- ZZi; try omega; clear (*XXi*) ZZi.
    unfold QByte.
(*    remember (UpdateOut ll (4 * i) xi) as l.*)
    remember (UpdateOut (hPosLoop3 (Z.to_nat i) xs OUT) (4 * i) (Znth (5 * i) xs)) as l.
    assert (ZLU: Zlength(UpdateOut l (16 + 4 * i) zi) = 32).
      rewrite UpdateOut_Zlength; trivial. omega. omega.
    rewrite (split3_data_at_Tarray_tuchar Tsh 32 (16 + 4 * i) (4+16 + 4 * i)); try omega.
(*      rewrite OC in *.*)
      rewrite field_address0_offset by auto with field_compatible.
      rewrite field_address0_offset by auto with field_compatible.
      unfold offset_val. Opaque QuadByte2ValList.  simpl. repeat rewrite Z.mul_1_l.
      Transparent QuadByte2ValList.
      unfold UpdateOut.
      autorewrite with sublist. Time cancel. (*0.6*)
      rewrite sublist_app2; autorewrite with sublist; try omega.
      rewrite sublist_app2; try rewrite <- QuadByteValList_ZLength; try omega.
      autorewrite with sublist. rewrite Zplus_comm. apply derives_refl'. f_equal. f_equal; omega. }
  Time entailer!. (*3.7 versus 12.8*) (*With temp _i (Vint (Int.repr 4)) in LOCAL of HTruePostCondL apply derives_refl.*)
Time Qed. (*June 4th, 2017 (laptop): Finished transaction in 3.433 secs (2.936u,0.008s) (successful)*)

Definition HTruePostCond (FR:mpred) t y x w nonce out c k h (xs:list int) ys data OUT :=
match data with ((Nonce, C), K) =>
(EX intsums:_,
  PROP (Zlength intsums = 16 /\
        (forall j, 0 <= j < 16 ->
           exists xj, exists yj,
           Znth j (map Vint xs) = Vint xj /\
           Znth j (map Vint ys) = Vint yj /\
           Znth j (map Vint intsums) = Vint (Int.add yj xj)))
  LOCAL (lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
  SEP (FR; CoreInSEP data (nonce, c, k); (*SByte Nonce nonce; SByte C c;
       ThirtyTwoByte K k;*)
       data_at Tsh (tarray tuint 16)
         (map Vint (hPosLoop2 4 intsums C Nonce)) x;
       data_at Tsh (tarray tuint 16) (map Vint ys) y;
       data_at Tsh (tarray tuchar 32)
          (hPosLoop3 4 (hPosLoop2 4 intsums C Nonce) OUT) out))
end.

Definition epilogue_htrue_statement:=
 Ssequence
     (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
        (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 16) tint) tint)
        (Ssequence
           (Sset _t'17
              (Ederef
                 (Ebinop Oadd (Evar _x (tarray tuint 16)) (Etempvar _i tint)
                    (tptr tuint)) tuint))
           (Ssequence
              (Sset _t'18
                 (Ederef
                    (Ebinop Oadd (Evar _y (tarray tuint 16))
                       (Etempvar _i tint) (tptr tuint)) tuint))
              (Sassign
                 (Ederef
                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                       (Etempvar _i tint) (tptr tuint)) tuint)
                 (Ebinop Oadd (Etempvar _t'17 tuint) (Etempvar _t'18 tuint)
                    tuint))))
        (Sset _i
           (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint)))
     (Ssequence
        (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
           (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 4) tint) tint)
           (Ssequence
              (Ssequence
                 (Scall (Some _t'9)
                    (Evar _ld32
                       (Tfunction (Tcons (tptr tuchar) Tnil) tuint cc_default))
                    [Ebinop Oadd (Etempvar _c (tptr tuchar))
                       (Ebinop Omul (Econst_int (Int.repr 4) tint)
                          (Etempvar _i tint) tint) (tptr tuchar)])
                 (Ssequence
                    (Sset _t'16
                       (Ederef
                          (Ebinop Oadd (Evar _x (tarray tuint 16))
                             (Ebinop Omul (Econst_int (Int.repr 5) tint)
                                (Etempvar _i tint) tint) (tptr tuint)) tuint))
                    (Sassign
                       (Ederef
                          (Ebinop Oadd (Evar _x (tarray tuint 16))
                             (Ebinop Omul (Econst_int (Int.repr 5) tint)
                                (Etempvar _i tint) tint) (tptr tuint)) tuint)
                       (Ebinop Osub (Etempvar _t'16 tuint)
                          (Etempvar _t'9 tuint) tuint))))
              (Ssequence
                 (Scall (Some _t'10)
                    (Evar _ld32
                       (Tfunction (Tcons (tptr tuchar) Tnil) tuint cc_default))
                    [Ebinop Oadd (Etempvar _in (tptr tuchar))
                       (Ebinop Omul (Econst_int (Int.repr 4) tint)
                          (Etempvar _i tint) tint) (tptr tuchar)])
                 (Ssequence
                    (Sset _t'15
                       (Ederef
                          (Ebinop Oadd (Evar _x (tarray tuint 16))
                             (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                                (Etempvar _i tint) tint) (tptr tuint)) tuint))
                    (Sassign
                       (Ederef
                          (Ebinop Oadd (Evar _x (tarray tuint 16))
                             (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                                (Etempvar _i tint) tint) (tptr tuint)) tuint)
                       (Ebinop Osub (Etempvar _t'15 tuint)
                          (Etempvar _t'10 tuint) tuint)))))
           (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                 tint)))
        (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
           (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 4) tint) tint)
           (Ssequence
              (Ssequence
                 (Sset _t'14
                    (Ederef
                       (Ebinop Oadd (Evar _x (tarray tuint 16))
                          (Ebinop Omul (Econst_int (Int.repr 5) tint)
                             (Etempvar _i tint) tint) (tptr tuint)) tuint))
                 (Scall None
                    (Evar _st32
                       (Tfunction (Tcons (tptr tuchar) (Tcons tuint Tnil))
                          tvoid cc_default))
                    [Ebinop Oadd (Etempvar _out (tptr tuchar))
                       (Ebinop Omul (Econst_int (Int.repr 4) tint)
                          (Etempvar _i tint) tint) (tptr tuchar);
                    Etempvar _t'14 tuint]))
              (Ssequence
                 (Sset _t'13
                    (Ederef
                       (Ebinop Oadd (Evar _x (tarray tuint 16))
                          (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                             (Etempvar _i tint) tint) (tptr tuint)) tuint))
                 (Scall None
                    (Evar _st32
                       (Tfunction (Tcons (tptr tuchar) (Tcons tuint Tnil))
                          tvoid cc_default))
                    [Ebinop Oadd
                       (Ebinop Oadd (Etempvar _out (tptr tuchar))
                          (Econst_int (Int.repr 16) tint) (tptr tuchar))
                       (Ebinop Omul (Econst_int (Int.repr 4) tint)
                          (Etempvar _i tint) tint) (tptr tuchar);
                    Etempvar _t'13 tuint])))
           (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                 tint)))).

Opaque hPosLoop2. Opaque hPosLoop3.

Lemma verif_fcore_epilogue_htrue Espec (FR:mpred) t y x w nonce out c k h (OUT: list val) xs ys data:
@semax CompSpecs Espec
  (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs nil)
  (PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 20)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at Tsh (tarray tuchar 32) OUT out;
         CoreInSEP data (nonce, c, k);
         data_at Tsh (tarray tuint 16) (map Vint ys) y;
         data_at Tsh (tarray tuint 16) (map Vint xs) x))
epilogue_htrue_statement (normal_ret_assert (HTruePostCond FR t y x w nonce out c k h xs ys data OUT)).
Proof. intros.
freeze [0;1;2] FR1.
forward_seq. apply HTrue_loop1.
Intros sums.
destruct H as [SL [intsums [? HSums1]]]; subst sums. rewrite Zlength_map in SL.
drop_LOCAL 0%nat. (*VST: deadvars fails*)
thaw FR1. freeze [0;1;3] FR2.
destruct data as ((Nonce, C), K).
forward_seq. apply HTrue_loop2.
drop_LOCAL 0%nat. (*VST: deadvars fails*)
thaw FR2. freeze [0;2;3] FR3.
eapply semax_post_flipped'.  apply HTrue_loop3.
Exists intsums. Time entailer!.
  intros j J.
  destruct (HSums1 _ J) as [xj [Xj [X _]]].
  destruct X as [yj [Yi Sj]]. apply J.
  exists xj, yj. auto.
thaw FR3. (*subst c k nonce.*) unfold CoreInSEP. Time cancel. (*0.1 penalty*)
Time Qed. (*June 4th, 2017 (laptop): Finished transaction in 1.192 secs (0.719u,0.012s) (successful) *)
