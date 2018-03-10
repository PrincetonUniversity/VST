Require Import Recdef.
Require Import VST.floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.

Require Import tweetnacl20140427.split_array_lemmas.
Require Import ZArith.
Require Import tweetnacl20140427.tweetNaclBase.
Require Import tweetnacl20140427.Salsa20.
Require Import tweetnacl20140427.tweetnaclVerifiableC.
Require Import tweetnacl20140427.verif_salsa_base.

Require Import tweetnacl20140427.spec_salsa. Opaque Snuffle.Snuffle. Opaque fcore_result.

Definition X_content (x: SixteenByte * SixteenByte * (SixteenByte * SixteenByte))
                     (i:Z) (l:list val) : Prop :=
    l = upd_upto x (Z.to_nat i) (list_repeat 16 Vundef).

Lemma XcontUpdate Nonce C Key1 Key2 i l
      (I: 0 <= i < 4)
      (L: X_content (Nonce, C, (Key1, Key2)) i l):
X_content (Nonce, C, (Key1, Key2)) (i + 1)
  (upd_Znth (11 + i)
     (upd_Znth (6 + i)
        (upd_Znth (1 + i)
           (upd_Znth (5 * i) l
              (Vint (littleendian (Select16Q C i))))
           (Vint (littleendian (Select16Q Key1 i))))
        (Vint (littleendian (Select16Q Nonce i))))
     (Vint (littleendian (Select16Q Key2 i)))).
Proof. unfold X_content in *.
  rewrite (Z.add_comm _ 1), Z2Nat.inj_add; try omega. simpl.
  rewrite Z2Nat.id; try omega. subst l; reflexivity.
Qed.

(*Issue : writing the lemma using the Delta := func_typcontext ...
  @semax CompSepcs Espec Delta ...
  leads to failure - but only 40 lines down, in the call to forward_call,
  where check_Delta now fails since it introduces a Delta0.
  I think we need to complement the line (
    Delta := @abbreviate tycontext (mk_tycontext _ _ _ _ _) |- _ => ...
  in checkDelta (checkDeltaOLD) with a second option,
  Delta := func_tycontext ... =>.
  Note that
  1. rerunning abbreviate_semax at that place (before calling forward_call)
     does not resolve the situation
  2. In the master-branch, we actually could write the lemma using Delta :=,
     so this is really an issue ith the new_compcert branch*)

Lemma f_core_loop1 (Espec : OracleKind) FR c k h nonce out w x y t
(data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte))
(*(Delta := func_tycontext f_core SalsaVarSpecs SalsaFunSpecs) *):
@semax CompSpecs Espec
  (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs nil) (*Delta*)
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
           lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
           temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR; data_at_ Tsh (tarray tuint 16) x;
         CoreInSEP data (nonce, c, k)))

  (Sfor (Sset _i (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 4) tint) tint)
     (Ssequence
        (Ssequence
           (Scall (Some _t'1)
              (Evar _ld32
                 (Tfunction (Tcons (tptr tuchar) Tnil) tuint cc_default))
              [Ebinop Oadd (Etempvar _c (tptr tuchar))
                 (Ebinop Omul (Econst_int (Int.repr 4) tint)
                    (Etempvar _i tint) tint) (tptr tuchar)])
           (Sassign
              (Ederef
                 (Ebinop Oadd (Evar _x (tarray tuint 16))
                    (Ebinop Omul (Econst_int (Int.repr 5) tint)
                       (Etempvar _i tint) tint) (tptr tuint)) tuint)
              (Etempvar _t'1 tuint)))
        (Ssequence
           (Ssequence
              (Scall (Some _t'2)
                 (Evar _ld32
                    (Tfunction (Tcons (tptr tuchar) Tnil) tuint cc_default))
                 [Ebinop Oadd (Etempvar _k (tptr tuchar))
                    (Ebinop Omul (Econst_int (Int.repr 4) tint)
                       (Etempvar _i tint) tint) (tptr tuchar)])
              (Sassign
                 (Ederef
                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                       (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                          (Etempvar _i tint) tint) (tptr tuint)) tuint)
                 (Etempvar _t'2 tuint)))
           (Ssequence
              (Ssequence
                 (Scall (Some _t'3)
                    (Evar _ld32
                       (Tfunction (Tcons (tptr tuchar) Tnil) tuint cc_default))
                    [Ebinop Oadd (Etempvar _in (tptr tuchar))
                       (Ebinop Omul (Econst_int (Int.repr 4) tint)
                          (Etempvar _i tint) tint) (tptr tuchar)])
                 (Sassign
                    (Ederef
                       (Ebinop Oadd (Evar _x (tarray tuint 16))
                          (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                             (Etempvar _i tint) tint) (tptr tuint)) tuint)
                    (Etempvar _t'3 tuint)))
              (Ssequence
                 (Scall (Some _t'4)
                    (Evar _ld32
                       (Tfunction (Tcons (tptr tuchar) Tnil) tuint cc_default))
                    [Ebinop Oadd
                       (Ebinop Oadd (Etempvar _k (tptr tuchar))
                          (Econst_int (Int.repr 16) tint) (tptr tuchar))
                       (Ebinop Omul (Econst_int (Int.repr 4) tint)
                          (Etempvar _i tint) tint) (tptr tuchar)])
                 (Sassign
                    (Ederef
                       (Ebinop Oadd (Evar _x (tarray tuint 16))
                          (Ebinop Oadd (Econst_int (Int.repr 11) tint)
                             (Etempvar _i tint) tint) (tptr tuint)) tuint)
                    (Etempvar _t'4 tuint))))))
     (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))
  (normal_ret_assert (
PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 4)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR;
         EX  l : list val, !!X_content data 4 l &&
                 data_at Tsh (tarray tuint 16) l x;
         CoreInSEP data (nonce, c, k)))).
Proof. intros. abbreviate_semax.
Time forward_for_simple_bound 4 (EX i:Z,
   PROP  ()
   LOCAL  (
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FR;
         EX l:_, !!(X_content data i l) && data_at Tsh (tarray tuint 16) l x;
         CoreInSEP data (nonce, c, k))). (*0.8 versus 2.1*)
{ Exists (list_repeat 16 Vundef). Time entailer!. (*1.3 versus 4.2*) }
{ rename H into I.

  destruct data as ((Nonce, C), Key). unfold CoreInSEP.
  unfold SByte at 2. Intros X0; rename H into X0cont.

  freeze [0;2;4] FR1.
  freeze [0;1] FR2.

  assert (C16:= SixteenByte2ValList_Zlength C).
  remember (SplitSelect16Q C i) as FB; destruct FB as (Front, Back).
  Time assert_PROP (isptr c /\ field_compatible (Tarray tuchar 16 noattr) [] c) as FCc by entailer!. (*2.1 versus 3.7*)
  destruct FCc as [Pc FC]; apply isptrD in Pc; destruct Pc as [cb [coff CP]]; rewrite CP in *.
  destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB I) as [FL _].

  rewrite (split3_data_at_Tarray_tuchar Tsh 16 (Zlength (QuadChunks2ValList Front))
        (Zlength (QuadChunks2ValList Front) + Zlength (QuadChunks2ValList [Select16Q C i])));
    repeat rewrite QuadChunk2ValList_ZLength;
    try rewrite FL; try rewrite <- C1; try rewrite Zlength_cons, Zlength_nil; try solve[simpl; omega].
  rewrite Zminus_plus. change (Z.succ 0) with 1. repeat rewrite Z.mul_1_r.
  Time normalize. (*2 versus 2.8*)
  rewrite (Select_SplitSelect16Q C i _ _ HeqFB) at 2.
  rewrite field_address0_offset by auto with field_compatible.
  rewrite field_address0_offset by auto with field_compatible. simpl.
  autorewrite with sublist.
  rewrite sublist_app2; (*. (4 * Zlength Front) (4 + 4 * Zlength Front)); *)
    repeat rewrite QuadChunk2ValList_ZLength; repeat rewrite FL.
    2: omega.
  rewrite Zminus_diag. rewrite Z.add_simpl_l. repeat rewrite Z.mul_1_l.

  freeze [0;2;3] FR3.
  rewrite (sublist0_app1 4), (sublist_same 0 4); try rewrite <- QuadByteValList_ZLength; try omega.

  (*Issue this is where the call fails if we use abbreviation Delta := ... in the statement of the lemma*)


  Time forward_call (offset_val (4 * i) (Vptr cb coff), Select16Q C i). (*3.4 versus 15.4*)
  (*{ goal automatically discharged versus 4.2 }*)

  thaw FR3. 
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL  ( temp _t'1 (Vint (littleendian (Select16Q C i)));
   temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP
   (FRZL FR2; data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList C) c))).
  { rewrite (Select_SplitSelect16Q C i _ _ HeqFB). unfold QByte.
    rewrite (split3_data_at_Tarray_tuchar Tsh 16 (Zlength (QuadChunks2ValList Front)) (Zlength (QuadChunks2ValList Front)+4)); trivial;
    repeat rewrite Zlength_app;
    repeat rewrite QuadChunk2ValList_ZLength;
(*    repeat rewrite FL; try rewrite BL; *)
    try rewrite <- QuadByteValList_ZLength; try rewrite Z.mul_1_r; try omega.
     2: destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB I) as [_ BL]; rewrite FL, BL; omega.
    autorewrite with sublist.
    rewrite CP in *.
    rewrite field_address0_offset by auto with field_compatible.
    rewrite field_address0_offset by auto with field_compatible.
    Time entailer!. (*7.8*)
    rewrite app_nil_r.
    apply sepcon_derives. autorewrite with sublist.
      rewrite sublist_app2; repeat rewrite QuadChunk2ValList_ZLength; repeat rewrite FL; try omega.
      repeat rewrite Zminus_diag. rewrite Z.add_simpl_l.
      rewrite sublist_app1; try rewrite <- QuadByteValList_ZLength; try omega.
      rewrite sublist_same; try rewrite <- QuadByteValList_ZLength; try omega. apply derives_refl.
    rewrite sublist_app2; repeat rewrite QuadChunk2ValList_ZLength; repeat rewrite FL; try omega.
    repeat rewrite Z.add_simpl_l, app_nil_r in *. apply derives_refl. }

  (*Store into x[...]*)
  thaw FR2.
  freeze [0;2] FR4.
  Time forward. (*2.5 versus 5.8*)

  destruct Key as [Key1 Key2].
  thaw FR4.
  Opaque ThirtyTwoByte.
  thaw FR1.
  freeze [0;1;3;4] FR5. Transparent ThirtyTwoByte.
  Time assert_PROP (field_compatible (Tarray tuchar 32 noattr) [] k) as FCK32
    by (unfold ThirtyTwoByte; entailer!). (*1.1 versus 5.1*)
  erewrite ThirtyTwoByte_split16; trivial. unfold SByte at 1. Opaque ThirtyTwoByte.
  Time normalize. (*2.2 versus 3.8*)
  Time assert_PROP (field_compatible (Tarray tuchar 16 noattr) [] k) as FCK16 by entailer!. (*1 versus 4.7*)
  assert (K1_16:= SixteenByte2ValList_Zlength Key1).
  remember (SplitSelect16Q Key1 i) as FB_K1. destruct FB_K1 as (Front_K1, Back_K1).
(*  rewrite (Select_SplitSelect16Q Key1 i _ _ HeqFB_K1).*)
  erewrite Select_Unselect_Tarray_at. (*; repeat rewrite <- K1_16; trivial.*)
    2: symmetry; apply (Select_SplitSelect16Q Key1 i _ _ HeqFB_K1).
    2: assumption.
    2: rewrite <- (Select_SplitSelect16Q Key1 i _ _ HeqFB_K1), <- K1_16; trivial.
    2: rewrite <- (Select_SplitSelect16Q Key1 i _ _ HeqFB_K1), <- K1_16; cbv; trivial.
  unfold Select_at. simpl. rewrite app_nil_r. flatten_sepcon_in_SEP.
  freeze [1;2;3] FR6.
  (*assert (FrontBackK1:= (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_K1 I)) as [FLK BLK].*)
  rewrite <- QuadByteValList_ZLength. (*rewrite Z.mul_1_l. *)
  rewrite  QuadChunk2ValList_ZLength.
  destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_K1 I) as [FLK _]; rewrite FLK.

  Time forward_call (offset_val (4 * i) k,
                 Select16Q Key1 i). (*8.9 versus 19.5; both were 3-4 secs faster befor tick elimination etc*)

  thaw  FR6.
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL  (temp _t'2 (Vint (littleendian (Select16Q Key1 i)));
   temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FRZL FR5; ThirtyTwoByte (Key1,Key2) k))).
  { erewrite ThirtyTwoByte_split16; trivial.
    repeat rewrite  <- QuadByteValList_ZLength; repeat rewrite QuadChunk2ValList_ZLength.
    Time entailer!. (*4.4 versus 6.6*)
    unfold SByte. rewrite (Select_SplitSelect16Q _ _ _ _ HeqFB_K1) in *.
    erewrite Select_Unselect_Tarray_at with (data:= QuadChunks2ValList Front_K1 ++
       QuadChunks2ValList [Select16Q Key1 (Zlength Front)(*i*)] ++ QuadChunks2ValList Back_K1); try reflexivity.
    + unfold QByte, Select_at. simpl. repeat rewrite app_nil_r.
      unfold Unselect_at.
      rewrite  QuadChunk2ValList_ZLength.
      rewrite <- QuadByteValList_ZLength, FLK. cancel.
    + assumption.
    + rewrite <- K1_16; assumption.
    + rewrite <- K1_16. cbv; trivial.
  }

  (*Store into x[...]*)
  thaw FR5.
  freeze [0;1;2;4] FR6.
  Time forward. (*2.8 versus 7.8*)

  (*Load nonce*)
  thaw FR6. freeze [0;2;3;4] FR7.
  unfold SByte at 1; simpl.
  assert (N16:= SixteenByte2ValList_Zlength Nonce).
  remember (SplitSelect16Q Nonce i) as FB_N; destruct FB_N as (Front_N, BACK_N).
    rewrite (Select_SplitSelect16Q _ i _ _ HeqFB_N) in *.
  Time assert_PROP (field_compatible (Tarray tuchar 16 noattr) [] nonce) as FCN by entailer!. (*1.2 versus 6.8*)
  erewrite Select_Unselect_Tarray_at with (d:=nonce); try reflexivity; try assumption.
  2: solve [rewrite <- N16; trivial].
  2: solve [rewrite <- N16; cbv; trivial].
  Time normalize. (*2.4 versus 5.2*)
  freeze [1;2] FR8.
  unfold Select_at. simpl. rewrite app_nil_r.
  rewrite <- QuadByteValList_ZLength. (*rewrite Z.mul_1_l.  simpl.*)
  rewrite  QuadChunk2ValList_ZLength.
  destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_N I) as [FrontN _]; rewrite FrontN.
  (*destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_N I) as [FrontN BackN].*)

  Time forward_call (offset_val (4 * i) nonce,
                 Select16Q Nonce i). (*11.7 versus 21*)

  thaw FR8.
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL  (
   temp _t'3 (Vint (littleendian (Select16Q Nonce i)));
   temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP (FRZL FR7; SByte Nonce nonce))).
  { Time entailer!. (*1.8 versus 9.5*)

    (*Apart from the unfold QByte, the next 9 lines are exactly as above, inside the function call*)
    unfold SByte. rewrite (Select_SplitSelect16Q _ _ _ _ HeqFB_N) in *.
    erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption.
    + unfold QByte, Select_at. simpl. rewrite app_nil_r. cancel.
      rewrite <- QuadByteValList_ZLength. (*rewrite Z.mul_1_l. simpl.*)
      rewrite  QuadChunk2ValList_ZLength.
      (*destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_N I) as [FrontN _]; rewrite FrontN; cancel.*)
      rewrite FrontN; cancel.
    + rewrite <- N16; trivial.
    + rewrite <- N16; cbv; trivial. }

  (*Store into x[...]*)
  thaw FR7. freeze [0;1;2;4] FR9.
  Time forward. (*3.2 versus 15*)

  (*Load Key2*)
  thaw FR9. freeze [0;1;3;4] FR10.
  rewrite ThirtyTwoByte_split16; trivial. Time normalize. (*2.2 versus 4.1*)
  unfold SByte at 2.
  assert (K2_16:= SixteenByte2ValList_Zlength Key2).
  Time assert_PROP (isptr k/\ field_compatible (Tarray tuchar 16 noattr) [] (offset_val 16 k))
     as Pk_FCK2 by entailer!. (*1.4 versus 6.6*)
  destruct Pk_FCK2 as [Pk FCK2]; apply isptrD in Pk; destruct Pk as [kb [koff Pk]]; rewrite Pk in *.
  remember (SplitSelect16Q Key2 i) as FB_K2; destruct FB_K2 as (Front_K2, Back_K2).
  rewrite (Select_SplitSelect16Q _ i _ _ HeqFB_K2) in *.
  erewrite Select_Unselect_Tarray_at with (d:=offset_val 16 (Vptr kb koff)); try reflexivity; try assumption.
  2: solve [rewrite <- K2_16; trivial]. 2: solve [rewrite <- K2_16; cbv; trivial].
  Time normalize. (*1.4 versus 6.6*)
  unfold Select_at. simpl. rewrite app_nil_r.
  repeat rewrite <- QuadByteValList_ZLength.
  rewrite QuadChunk2ValList_ZLength.

  freeze [1;2;3] FR11.
  Time forward_call (Vptr kb
           (Ptrofs.add (Ptrofs.add koff (Ptrofs.repr 16)) (Ptrofs.repr (4 * Zlength Front_K2))),
                 Select16Q Key2 i). (*8.9 versus 20.5 SLOW*)
  { destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_K2 I) as [FK2 _]; rewrite FK2.
     apply prop_right; simpl. unfold Ptrofs.of_ints; simpl; normalize. }

  thaw FR11.
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL  ( 
   temp _t'4 (Vint (littleendian (Select16Q Key2 i)));
   temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (FRZL FR10; ThirtyTwoByte (Key1,Key2) k))).
  { rewrite Pk in *. erewrite ThirtyTwoByte_split16 by assumption.
    Time entailer!. (*4.6 versus 7.4*)

    (*Apart from the unfold QByte, the next 9 lines are exactly as above, inside the function call*)
    unfold SByte. rewrite (Select_SplitSelect16Q _ _ _ _ HeqFB_K2) in *.
    erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption.
    + unfold QByte, Select_at. simpl. repeat rewrite app_nil_r. cancel.
      rewrite <- QuadByteValList_ZLength. (*rewrite Z.mul_1_l. simpl.*)
      rewrite  QuadChunk2ValList_ZLength. rewrite Ptrofs.add_assoc. rewrite ptrofs_add_repr. cancel.
    + rewrite <- K2_16; assumption.
    + rewrite <- K2_16; cbv; trivial. }

  (*Store into x[...]*)
  thaw FR10. freeze [0;1;2;4] FR11.
  Time forward. (*4.3 versus 14.7*) clear FL.

  Time entailer!. (*4.9 versus 16.1*)  remember (Zlength Front_K1) as i.
  Exists (upd_Znth (11 + i)
     (upd_Znth (6 + i)
        (upd_Znth (1 + i)
           (upd_Znth (5 * i) X0
              (Vint (littleendian (Select16Q C i))))
           (Vint (littleendian (Select16Q Key1 i))))
        (Vint (littleendian (Select16Q Nonce i))))
     (Vint (littleendian (Select16Q Key2 i)))).
  Time entailer!. (*2 versus 2.8  - penalty*)
    clear - X0cont I. apply XcontUpdate; trivial.

  thaw FR11. Time cancel. (*0.3*)
  apply derives_refl.
 }
apply andp_left2; apply derives_refl.
Time Qed. (*VST 20.: 5.5s*) (* 19.046 secs (17.109u,0.015s) (successful)*)

Lemma XX data l: X_content data 4 l ->
  l = match data with ((Nonce, C), (Key1, Key2)) =>
          match Nonce with (N1, N2, N3, N4) =>
          match C with (C1, C2, C3, C4) =>
          match Key1 with (K1, K2, K3, K4) =>
          match Key2 with (L1, L2, L3, L4) =>
      map Vint (map littleendian [C1; K1; K2; K3;
                                  K4; C2; N1; N2;
                                  N3; N4; C3; L1;
                                  L2; L3; L4; C4])
      end end end end end.
Proof.
intros. red in H. subst l.
apply upd_upto_char. reflexivity.
Qed.