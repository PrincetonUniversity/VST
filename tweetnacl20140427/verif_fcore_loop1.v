Require Import Recdef.
Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import general_lemmas.
Require Import sublist.

Require Import split_array_lemmas.
Require Import ZArith. 
Require Import tweetNaclBase.
Require Import Salsa20.
Require Import tweetnaclVerifiableC.
Require Import verif_salsa_base.

Require Import spec_salsa. Opaque Snuffle.Snuffle. Opaque fcore_result.

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
Proof. unfold X_content in *. Opaque Z.add. Opaque Z.mul. simpl.
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

Lemma f_core_loop1: forall (Espec : OracleKind)
c k h nonce out OUT 
(data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte))
(*(Delta := func_tycontext f_core SalsaVarSpecs SalsaFunSpecs) *)
w x y t,
@semax CompSpecs Espec (func_tycontext f_core SalsaVarSpecs SalsaFunSpecs) (* Delta*)
  (PROP  ()
   LOCAL  (lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (data_at_ Tsh (tarray tuint 16) y;
   data_at_ Tsh (tarray tuint 4) t; data_at_ Tsh (tarray tuint 16) x;
   data_at_ Tsh (tarray tuint 16) w; CoreInSEP data (nonce, c, k);
   data_at Tsh (tarray tuchar 64) OUT out))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 4) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Scall (Some 177%positive)
              (Evar _ld32 (Tfunction (Tcons (tptr tuchar) Tnil) tuint
                            cc_default))
              ((Ebinop Oadd (Etempvar _c (tptr tuchar))
                 (Ebinop Omul (Econst_int (Int.repr 4) tint)
                   (Etempvar _i tint) tint) (tptr tuchar)) :: nil))
            (Sset _aux (Etempvar 177%positive tuint)))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _x (tarray tuint 16))
                  (Ebinop Omul (Econst_int (Int.repr 5) tint)
                    (Etempvar _i tint) tint) (tptr tuint)) tuint)
              (Etempvar _aux tuint))
            (Ssequence
              (Ssequence
                (Scall (Some 178%positive)
                  (Evar _ld32 (Tfunction (Tcons (tptr tuchar) Tnil) tuint
                                cc_default))
                  ((Ebinop Oadd (Etempvar _k (tptr tuchar))
                     (Ebinop Omul (Econst_int (Int.repr 4) tint)
                       (Etempvar _i tint) tint) (tptr tuchar)) :: nil))
                (Sset _aux (Etempvar 178%positive tuint)))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                      (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                        (Etempvar _i tint) tint) (tptr tuint)) tuint)
                  (Etempvar _aux tuint))
                (Ssequence
                  (Ssequence
                    (Scall (Some 179%positive)
                      (Evar _ld32 (Tfunction (Tcons (tptr tuchar) Tnil) tuint
                                    cc_default))
                      ((Ebinop Oadd (Etempvar _in (tptr tuchar))
                         (Ebinop Omul (Econst_int (Int.repr 4) tint)
                           (Etempvar _i tint) tint) (tptr tuchar)) :: nil))
                    (Sset _aux (Etempvar 179%positive tuint)))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _x (tarray tuint 16))
                          (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                            (Etempvar _i tint) tint) (tptr tuint)) tuint)
                      (Etempvar _aux tuint))
                    (Ssequence
                      (Ssequence
                        (Scall (Some 180%positive)
                          (Evar _ld32 (Tfunction (Tcons (tptr tuchar) Tnil)
                                        tuint cc_default))
                          ((Ebinop Oadd
                             (Ebinop Oadd (Etempvar _k (tptr tuchar))
                               (Econst_int (Int.repr 16) tint) (tptr tuchar))
                             (Ebinop Omul (Econst_int (Int.repr 4) tint)
                               (Etempvar _i tint) tint) (tptr tuchar)) ::
                           nil))
                        (Sset _aux (Etempvar 180%positive tuint)))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _x (tarray tuint 16))
                            (Ebinop Oadd (Econst_int (Int.repr 11) tint)
                              (Etempvar _i tint) tint) (tptr tuint)) tuint)
                        (Etempvar _aux tuint))))))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (normal_ret_assert (
PROP  ()
   LOCAL  (temp _i (Vint (Int.repr 4)); lvar _t (tarray tuint 4) t;
   lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
   lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
   temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (data_at_ Tsh (tarray tuint 16) y;
   data_at_ Tsh (tarray tuint 4) t;
   EX  l : list val,
     !!X_content data 4 l && data_at Tsh (tarray tuint 16) l x;
   data_at_ Tsh (tarray tuint 16) w; CoreInSEP data (nonce, c, k);
   data_at Tsh (tarray tuchar 64) OUT out))).
Proof. intros. abbreviate_semax.
Time forward_for_simple_bound 4 (EX i:Z, 
   PROP  ()
   LOCAL  ( 
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (data_at_ Tsh (tarray tuint 16) y;
   data_at_ Tsh (tarray tuint 4) t;
   EX l:_, !!(X_content data i l) && data_at Tsh (tarray tuint 16) l x;
   data_at_ Tsh (tarray tuint 16) w; CoreInSEP data (nonce, c, k);
   data_at Tsh (tarray tuchar 64) OUT out)). (*2.1*)
{ Exists (list_repeat 16 Vundef). Time entailer!. (*4.2*) }
{ rename H into I.
 
  destruct data as ((Nonce, C), Key). unfold CoreInSEP.
  unfold SByte at 2. Intros X0; rename H into X0cont.

  assert (C16:= SixteenByte2ValList_Zlength C).
  remember (SplitSelect16Q C i) as FB; destruct FB as (Front, Back).
  Time assert_PROP (isptr c /\ field_compatible (Tarray tuchar 16 noattr) [] c) as FCc by entailer!. (*3.7*)
  destruct FCc as [Pc FC]; apply isptrD in Pc; destruct Pc as [cb [coff CP]]; rewrite CP in *.
  destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB I) as [FL _].

  rewrite (split3_data_at_Tarray_tuchar Tsh 16 (Zlength (QuadChunks2ValList Front)) 
        (Zlength (QuadChunks2ValList Front) + Zlength (QuadChunks2ValList [Select16Q C i])));
    repeat rewrite QuadChunk2ValList_ZLength;
    try rewrite FL; try rewrite <- C1; try rewrite Zlength_cons, Zlength_nil; try solve[simpl; omega].
  rewrite Zminus_plus. change (Z.succ 0) with 1. repeat rewrite Z.mul_1_r.
  Time normalize.  (*2.8*)
  rewrite (Select_SplitSelect16Q C i _ _ HeqFB) at 2.
  rewrite field_address0_offset by auto with field_compatible.
  rewrite field_address0_offset by auto with field_compatible. simpl.  
  autorewrite with sublist. 
  rewrite sublist_app2; (*. (4 * Zlength Front) (4 + 4 * Zlength Front)); *)
    repeat rewrite QuadChunk2ValList_ZLength; repeat rewrite FL. 
    2: omega.
  rewrite Zminus_diag. rewrite Z.add_simpl_l. repeat rewrite Z.mul_1_l.
  rewrite (sublist0_app1 4), (sublist_same 0 4); try rewrite <- QuadByteValList_ZLength; try omega.

  (*Issue this is where the call fails if we use abbreviation Delta := ... in the statement of the lemma*)
  Time forward_call (Vptr cb (Int.add coff (Int.repr (4 * i))), Select16Q C i). (*16.3*)

  Intros pat; subst pat; simpl.
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL  ( temp _aux (Vint (littleendian (Select16Q C i)));
   temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP 
   (data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList C) c;
   SByte Nonce nonce;
   ThirtyTwoByte Key k;
   data_at_ Tsh (tarray tuint 16) y; data_at_ Tsh (tarray tuint 4) t;
   data_at Tsh (tarray tuint 16) X0 x;
   data_at_ Tsh (tarray tuint 16) w; 
   data_at Tsh (tarray tuchar 64) OUT out))). 
  { rewrite (Select_SplitSelect16Q C i _ _ HeqFB). unfold QByte.
    rewrite (split3_data_at_Tarray_tuchar Tsh 16 (Zlength (QuadChunks2ValList Front)) (4+Zlength (QuadChunks2ValList Front))); trivial;
    repeat rewrite Zlength_app; 
    repeat rewrite QuadChunk2ValList_ZLength;
(*    repeat rewrite FL; try rewrite BL; *)
    try rewrite <- QuadByteValList_ZLength; try rewrite Z.mul_1_r; try omega.
     2: destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB I) as [_ BL]; rewrite FL, BL; omega.
    autorewrite with sublist.
    Time entailer!. (*12.5*) 
    rewrite sublist_app2; repeat rewrite QuadChunk2ValList_ZLength; repeat rewrite FL; try omega.
    repeat rewrite Z.add_simpl_l, app_nil_r.
    rewrite field_address0_offset by auto with field_compatible.
    rewrite field_address0_offset by auto with field_compatible. simpl.
    repeat rewrite Z.mul_1_l. 
    rewrite sublist_app2; try rewrite <- QuadByteValList_ZLength; try omega.
    rewrite sublist_app2; try rewrite  QuadChunk2ValList_ZLength; try omega.
    rewrite sublist_app1; try rewrite <- QuadByteValList_ZLength; try omega.
    rewrite sublist_app2; try rewrite  QuadChunk2ValList_ZLength; try omega.
    rewrite sublist_app2; try rewrite <- QuadByteValList_ZLength; try omega.
    repeat rewrite Zminus_diag. rewrite Z.add_simpl_r.
    apply sepcon_derives.
      rewrite sublist_same; try rewrite <- QuadByteValList_ZLength; try omega. cancel.
    repeat rewrite Zminus_diag. rewrite Z.add_comm. cancel. }

  (*Store into x[...]*)
  Transparent firstn.
  Time forward. (*9.8*)

  destruct Key as [Key1 Key2]. 
  Time assert_PROP (field_compatible (Tarray tuchar 32 noattr) [] k) as FCK32 
    by (unfold ThirtyTwoByte; entailer!). (*5.1*)
  erewrite ThirtyTwoByte_split16; trivial. unfold SByte at 2.
  Time normalize. (*3.8*)
  Time assert_PROP (field_compatible (Tarray tuchar 16 noattr) [] k) as FCK16 by entailer!. (*4.7*)
  assert (K1_16:= SixteenByte2ValList_Zlength Key1).
  remember (SplitSelect16Q Key1 i) as FB_K1. destruct FB_K1 as (Front_K1, Back_K1).
(*  rewrite (Select_SplitSelect16Q Key1 i _ _ HeqFB_K1).*)
  erewrite Select_Unselect_Tarray_at. (*; repeat rewrite <- K1_16; trivial.*)
    2: symmetry; apply (Select_SplitSelect16Q Key1 i _ _ HeqFB_K1).
    2: assumption. 
    2: rewrite <- (Select_SplitSelect16Q Key1 i _ _ HeqFB_K1), <- K1_16; trivial.
    2: rewrite <- (Select_SplitSelect16Q Key1 i _ _ HeqFB_K1), <- K1_16; cbv; trivial.
  unfold Select_at. simpl. rewrite app_nil_r.
  (*assert (FrontBackK1:= (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_K1 I)) as [FLK BLK].*)
  rewrite <- QuadByteValList_ZLength. (*rewrite Z.mul_1_l. *)
  rewrite  QuadChunk2ValList_ZLength.

  Time forward_call (offset_val (Int.repr (4 * i)) k, 
                 Select16Q Key1 i). (*22.4*)
  { destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_K1 I) as [FLK _]; rewrite FLK.
    Time cancel. (*8.7*) }
  Intros v; subst v; simpl.

  apply semax_pre with (P':=
  (PROP  ()
   LOCAL  (temp _aux (Vint (littleendian (Select16Q Key1 i)));
   temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (ThirtyTwoByte (Key1,Key2) k;
   data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList C) c;
   SByte Nonce nonce; data_at_ Tsh (tarray tuint 16) y;
   data_at_ Tsh (tarray tuint 4) t;
   data_at Tsh (tarray tuint 16)
       (upd_Znth (5 * i) X0
          (Vint (littleendian (Select16Q C i)))) x;
   data_at_ Tsh (tarray tuint 16) w;
   data_at Tsh (tarray tuchar 64) OUT out))). 
  { erewrite ThirtyTwoByte_split16; trivial. 
    Time entailer!. (*6.6*)
    unfold SByte. rewrite (Select_SplitSelect16Q _ _ _ _ HeqFB_K1) in *.
    erewrite Select_Unselect_Tarray_at; try rewrite <- K1_16; try reflexivity; try assumption.
    unfold QByte, Select_at. simpl. repeat rewrite app_nil_r.
    rewrite  QuadChunk2ValList_ZLength.
    rewrite <- QuadByteValList_ZLength.
    destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_K1 I) as [FLK _]; rewrite FLK; cancel.
    rewrite <- K1_16; trivial. rewrite <- K1_16; cbv; trivial. }

  (*Store into x[...]*)
  Time forward. (* 13.6 SLOW was: 7.8*)

  (*Load nonce*)
  unfold SByte at 1; simpl.
  assert (N16:= SixteenByte2ValList_Zlength Nonce).
  remember (SplitSelect16Q Nonce i) as FB_N; destruct FB_N as (Front_N, BACK_N).
    rewrite (Select_SplitSelect16Q _ i _ _ HeqFB_N) in *. 
  Time assert_PROP (field_compatible (Tarray tuchar 16 noattr) [] nonce) as FCN by entailer!. (*6.8*)
  erewrite Select_Unselect_Tarray_at with (d:=nonce); try reflexivity; try assumption.
  Time normalize. (*5.2*)
  2: rewrite <- N16; trivial. 2: rewrite <- N16; cbv; trivial.
  unfold Select_at. simpl. rewrite app_nil_r.
  (*destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_N I) as [FrontN BackN].*)

  Time forward_call (offset_val (Int.repr (4 * i)) nonce, 
                 Select16Q Nonce i). (*22.8 SLOW*)
  { rewrite <- QuadByteValList_ZLength. (*rewrite Z.mul_1_l.  simpl.*)
    rewrite  QuadChunk2ValList_ZLength.
    destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_N I) as [FrontN _]; rewrite FrontN.
    Time cancel. (*4.2*)}
  
  Intros v; subst v; simpl.
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL  ((*temp _aux v; *)
   temp _aux (Vint (littleendian (Select16Q Nonce i)));
   temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP 
   (data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList C) c;
   SByte Nonce nonce;
   ThirtyTwoByte (Key1,Key2) k;
   data_at_ Tsh (tarray tuint 16) y; data_at_ Tsh (tarray tuint 4) t;
   data_at Tsh (tarray tuint 16)
       (upd_Znth (1 + i)
          (upd_Znth (5 * i) X0
             (Vint (littleendian (Select16Q C i))))
          (Vint (littleendian (Select16Q Key1 i)))) x;
   data_at_ Tsh (tarray tuint 16) w;
   data_at Tsh (tarray tuchar 64) OUT out (*data_block Tsh OUT out)*)))). 
  { Time entailer!. (*9.5*)
   
    (*Apart from the unfold QByte, the next 9 lines are exactly as above, inside the function call*)
    unfold SByte. rewrite (Select_SplitSelect16Q _ _ _ _ HeqFB_N) in *.
    erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption. 
    unfold QByte, Select_at. simpl. rewrite app_nil_r. cancel.
    rewrite <- QuadByteValList_ZLength. (*rewrite Z.mul_1_l. simpl.*)
    rewrite  QuadChunk2ValList_ZLength.
    destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_N I) as [FrontN _]; rewrite FrontN; cancel. 

    rewrite <- N16; trivial. rewrite <- N16; cbv; trivial. }

  (*Store into x[...]*)
  Time forward. (*15.7 SLOW; was 8.8 fore teick-eleimination*)

  (*Load Key2*)
  rewrite ThirtyTwoByte_split16; trivial. Time normalize. (*4.1*)
  unfold SByte at 2.
  assert (K2_16:= SixteenByte2ValList_Zlength Key2).
  Time assert_PROP (isptr k/\ field_compatible (Tarray tuchar 16 noattr) [] (offset_val (Int.repr 16) k))
     as Pk_FCK2 by entailer!. (*6.6*)
  destruct Pk_FCK2 as [Pk FCK2]; apply isptrD in Pk; destruct Pk as [kb [koff Pk]]; rewrite Pk in *. 
  remember (SplitSelect16Q Key2 i) as FB_K2; destruct FB_K2 as (Front_K2, Back_K2).
  rewrite (Select_SplitSelect16Q _ i _ _ HeqFB_K2) in *. 
  erewrite Select_Unselect_Tarray_at with (d:=offset_val (Int.repr 16) (Vptr kb koff)); try reflexivity; try assumption.
  2: rewrite <- K2_16; trivial. 2: rewrite <- K2_16; cbv; trivial.
  Time normalize. (*6.6*)
  unfold Select_at. simpl. rewrite app_nil_r.
  repeat rewrite <- QuadByteValList_ZLength.
  rewrite QuadChunk2ValList_ZLength.

  Time forward_call (Vptr kb
           (Int.add (Int.add koff (Int.repr 16)) (Int.repr (4 * Zlength Front_K2))),
                 Select16Q Key2 i). (*26 SLOW*)
  { destruct (Select_SplitSelect16Q_Zlength _ _ _ _ HeqFB_K2 I) as [FK2 _]; rewrite FK2.
     apply prop_right; simpl. do 2 rewrite Int.mul_commut, Int.mul_one. rewrite mul_repr. 
     trivial. }

  Intros v; subst v; simpl.
  apply semax_pre with (P':=
  (PROP  ()
   LOCAL  (
   temp _aux (Vint (littleendian (Select16Q Key2 i)));
   temp _i (Vint (Int.repr i));
   lvar _t (tarray tuint 4) t; lvar _y (tarray tuint 16) y;
   lvar _x (tarray tuint 16) x; lvar _w (tarray tuint 16) w; temp _in nonce;
   temp _out out; temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
   SEP  (ThirtyTwoByte (Key1,Key2) k;
   data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList C) c;
   SByte Nonce nonce; data_at_ Tsh (tarray tuint 16) y;
   data_at_ Tsh (tarray tuint 4) t;
   data_at Tsh (tarray tuint 16)
       (upd_Znth (6 + i)
          (upd_Znth (1 + i)
             (upd_Znth (5 * i) X0
                (Vint (littleendian (Select16Q C i))))
             (Vint (littleendian (Select16Q Key1 i))))
          (Vint (littleendian (Select16Q Nonce i)))) x;
   data_at_ Tsh (tarray tuint 16) w; 
   data_at Tsh (tarray tuchar 64) OUT out))). 
  { erewrite ThirtyTwoByte_split16. 2: rewrite Pk; assumption.
    Time entailer!. (*7.4*)
   
    (*Apart from the unfold QByte, the next 9 lines are exactly as above, inside the function call*)
    unfold SByte. rewrite (Select_SplitSelect16Q _ _ _ _ HeqFB_K2) in *.
    erewrite Select_Unselect_Tarray_at; try reflexivity; try assumption. 
    unfold QByte, Select_at. simpl. repeat rewrite app_nil_r. cancel.
    rewrite <- QuadByteValList_ZLength. (*rewrite Z.mul_1_l. simpl.*)
    rewrite  QuadChunk2ValList_ZLength. rewrite Int.add_assoc. rewrite add_repr. cancel.

    rewrite <- K2_16. assumption.
    rewrite <- K2_16. cbv; trivial. }

  (*Store into x[...]*)
  Time forward. (*14.7 SLOW; was 10.6*) clear FL.
  Time entailer!. (*11 SLOW*) 
  Exists (upd_Znth (11 + i)
     (upd_Znth (6 + i)
        (upd_Znth (1 + i)
           (upd_Znth (5 * i) X0
              (Vint (littleendian (Select16Q C i))))
           (Vint (littleendian (Select16Q Key1 i))))
        (Vint (littleendian (Select16Q Nonce i))))
     (Vint (littleendian (Select16Q Key2 i)))).
  Time entailer!. (*3.9*) 
    clear - X0cont I. apply XcontUpdate; trivial.
  apply derives_refl. }
apply derives_refl.
Time Qed. (*250*)

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