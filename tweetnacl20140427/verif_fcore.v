(* Functional implementation of Salsa20 whose
   structure matches the one of tweetnacl.c implementation,
   plus proof of coorrectness wrt Salsa20.v

   Lennart Beringer, June 2015*)
(*Processing time for this file: approx 13mins*)
Require Import VST.floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
(*Require Import general_lemmas.

Require Import split_array_lemmas.*)
Require Import ZArith.
Require Import tweetnacl20140427.tweetNaclBase.
Require Import tweetnacl20140427.Salsa20.
Require Import tweetnacl20140427.verif_salsa_base.
Require Import tweetnacl20140427.tweetnaclVerifiableC.
Require Import tweetnacl20140427.Snuffle.
Require Import tweetnacl20140427.spec_salsa.

Require Import tweetnacl20140427.verif_fcore_loop1.
Require Import tweetnacl20140427.verif_fcore_loop2.
Require Import tweetnacl20140427.verif_fcore_loop3.

Require Import tweetnacl20140427.verif_fcore_epilogue_htrue.
Require Import tweetnacl20140427.verif_fcore_epilogue_hfalse.

Opaque littleendian_invert. Opaque Snuffle.Snuffle.

Lemma HFalse_inv16_char: forall l xs ys,
  HFalse_inv l 16 xs ys ->
  Zlength xs = 16 -> Zlength ys=16 ->
  exists sum, Some sum = sumlist xs ys /\
  l = QuadChunks2ValList (map littleendian_invert sum).
Proof. intros. destruct H.
 destruct (listGE16 l) as
  [v0 [v1 [v2 [v3 [v4 [v5 [v6 [v7 [v8 [v9 [v10 [v11 [v12 [v13 [v14 [v15 [t1 [T1 L1]]]]]]]]]]]]]]]]]]. omega.
 rewrite H in L1; simpl in L1.
 destruct (listGE16 t1) as
  [v16 [v17 [v18 [v19 [v20 [v21 [v22 [v23 [v24 [v25 [v26 [v27 [v28 [v29 [v30 [v31 [t2 [T2 L2]]]]]]]]]]]]]]]]]]. omega.
 rewrite L1 in L2; simpl in L2.
 destruct (listGE16 t2) as
  [v32 [v33 [v34 [v35 [v36 [v37 [v38 [v39 [v40 [v41 [v42 [v43 [v44 [v45 [v46 [v47 [t3 [T3 L3]]]]]]]]]]]]]]]]]]. omega.
 rewrite L2 in L3; simpl in L3.
 destruct (listGE16 t3) as
  [v48 [v49 [v50 [v51 [v52 [v53 [v54 [v55 [v56 [v57 [v58 [v59 [v60 [v61 [v62 [v63 [t4 [T4 L4]]]]]]]]]]]]]]]]]]. omega.
 rewrite L3 in L4; simpl in L4.
 apply Zlength_nil_inv in L4. subst t3 t4 t2 t1. clear L1 L2 L3 H. simpl in T1.
 destruct (listD16 _ H0) as
  [x0 [x1 [x2 [x3 [x4 [x5 [x6 [x7 [x8 [x9 [x10 [x11 [x12 [x13 [x14 [x15 A1]]]]]]]]]]]]]]]].
 destruct (listD16 _ H1) as
  [y0 [y1 [y2 [y3 [y4 [y5 [y6 [y7 [y8 [y9 [y10 [y11 [y12 [y13 [y14 [y15 B1]]]]]]]]]]]]]]]].
subst l xs ys.
eexists; split. reflexivity.
unfold Znth in H2. simpl.
destruct (H2 0) as [x [X [y [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y. rewrite <- Q; clear Q.
destruct (H2 1) as [x [X [y [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y. rewrite <- Q; clear Q.
destruct (H2 2) as [x [X [y [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y. rewrite <- Q; clear Q.
destruct (H2 3) as [x [X [y [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y. rewrite <- Q; clear Q.
destruct (H2 4) as [x [X [y [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y. rewrite <- Q; clear Q.
destruct (H2 5) as [x [X [y [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y. rewrite <- Q; clear Q.
destruct (H2 6) as [x [X [y [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y. rewrite <- Q; clear Q.
destruct (H2 7) as [x [X [y [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y. rewrite <- Q; clear Q.
destruct (H2 8) as [x [X [y [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y. rewrite <- Q; clear Q.
destruct (H2 9) as [x [X [y [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y. rewrite <- Q; clear Q.
destruct (H2 10) as [x [X [y [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y. rewrite <- Q; clear Q.
destruct (H2 11) as [x [X [y [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y. rewrite <- Q; clear Q.
destruct (H2 12) as [x [X [y [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y. rewrite <- Q; clear Q.
destruct (H2 13) as [x [X [y [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y. rewrite <- Q; clear Q.
destruct (H2 14) as [x [X [y [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y. rewrite <- Q; clear Q.
destruct (H2 15) as [x [X [y [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y. rewrite <- Q; clear Q.
reflexivity.
Qed.

Lemma TP C1 C2 C3 C4 N1 N2 N3 N4 intsums OUT: Zlength intsums = 16 -> Zlength OUT = 32 ->
  hPosLoop3 4 (hPosLoop2 4 intsums (C1, C2, C3, C4) (N1, N2, N3, N4)) OUT =
 QuadByte2ValList (littleendian_invert (Int.sub (Znth 0 intsums)  (littleendian C1))) ++
 QuadByte2ValList (littleendian_invert (Int.sub (Znth 5 intsums)  (littleendian C2))) ++
 QuadByte2ValList (littleendian_invert (Int.sub (Znth 10 intsums) (littleendian C3))) ++
 QuadByte2ValList (littleendian_invert (Int.sub (Znth 15 intsums) (littleendian C4))) ++
 QuadByte2ValList (littleendian_invert (Int.sub (Znth 6 intsums)  (littleendian N1))) ++
 QuadByte2ValList (littleendian_invert (Int.sub (Znth 7 intsums)  (littleendian N2))) ++
 QuadByte2ValList (littleendian_invert (Int.sub (Znth 8 intsums)  (littleendian N3))) ++
 QuadByte2ValList (littleendian_invert (Int.sub (Znth 9 intsums)  (littleendian N4))).
Proof. intros.
rewrite Zlength_length in H, H0. simpl in H, H0.
destruct intsums; simpl in H. omega. rename i into v0.
destruct intsums; simpl in H. omega. rename i into v1.
destruct intsums; simpl in H. omega. rename i into v2.
destruct intsums; simpl in H. omega. rename i into v3.
destruct intsums; simpl in H. omega. rename i into v4.
destruct intsums; simpl in H. omega. rename i into v5.
destruct intsums; simpl in H. omega. rename i into v6.
destruct intsums; simpl in H. omega. rename i into v7.
destruct intsums; simpl in H. omega. rename i into v8.
destruct intsums; simpl in H. omega. rename i into v9.
destruct intsums; simpl in H. omega. rename i into v10.
destruct intsums; simpl in H. omega. rename i into v11.
destruct intsums; simpl in H. omega. rename i into v12.
destruct intsums; simpl in H. omega. rename i into v13.
destruct intsums; simpl in H. omega. rename i into v14.
destruct intsums; simpl in H. omega. rename i into v15.
destruct intsums; simpl in H. 2: omega. clear H. simpl.
unfold Znth. simpl.
destruct OUT; simpl in H0. omega. rename v into u0.
destruct OUT; simpl in H0. omega. rename v into u1.
destruct OUT; simpl in H0. omega. rename v into u2.
destruct OUT; simpl in H0. omega. rename v into u3.
destruct OUT; simpl in H0. omega. rename v into u4.
destruct OUT; simpl in H0. omega. rename v into u5.
destruct OUT; simpl in H0. omega. rename v into u6.
destruct OUT; simpl in H0. omega. rename v into u7.
destruct OUT; simpl in H0. omega. rename v into u8.
destruct OUT; simpl in H0. omega. rename v into u9.
destruct OUT; simpl in H0. omega. rename v into u10.
destruct OUT; simpl in H0. omega. rename v into u11.
destruct OUT; simpl in H0. omega. rename v into u12.
destruct OUT; simpl in H0. omega. rename v into u13.
destruct OUT; simpl in H0. omega. rename v into u14.
destruct OUT; simpl in H0. omega. rename v into u15.
destruct OUT; simpl in H0. omega. rename v into u16.
destruct OUT; simpl in H0. omega. rename v into u17.
destruct OUT; simpl in H0. omega. rename v into u18.
destruct OUT; simpl in H0. omega. rename v into u19.
destruct OUT; simpl in H0. omega. rename v into u20.
destruct OUT; simpl in H0. omega. rename v into u21.
destruct OUT; simpl in H0. omega. rename v into u22.
destruct OUT; simpl in H0. omega. rename v into u23.
destruct OUT; simpl in H0. omega. rename v into u24.
destruct OUT; simpl in H0. omega. rename v into u25.
destruct OUT; simpl in H0. omega. rename v into u26.
destruct OUT; simpl in H0. omega. rename v into u27.
destruct OUT; simpl in H0. omega. rename v into u28.
destruct OUT; simpl in H0. omega. rename v into u29.
destruct OUT; simpl in H0. omega. rename v into u30.
destruct OUT; simpl in H0. omega. rename v into u31.
destruct OUT; simpl in H0. 2: omega. clear H0. simpl. reflexivity. omega. omega.
Qed.

Definition HTrue_inv intsums xs ys:Prop:=
Zlength intsums = 16 /\
        (forall j, 0 <= j < 16 ->
           exists xj, exists yj,
           Znth j (map Vint xs) = Vint xj /\
           Znth j (map Vint ys) = Vint yj /\
           Znth j (map Vint intsums) = Vint (Int.add yj xj)).

Lemma HTrue_inv_char l xs ys: Zlength xs = 16 -> Zlength ys=16 ->
      HTrue_inv l xs ys -> Some l = sumlist xs ys.
Proof. rewrite sumlist_symm. intros LX LY [H L].
 destruct (listD16 _ LX) as
  [x0 [x1 [x2 [x3 [x4 [x5 [x6 [x7 [x8 [x9 [x10 [x11 [x12 [x13 [x14 [x15 A1]]]]]]]]]]]]]]]].
 destruct (listD16 _ LY) as
  [y0 [y1 [y2 [y3 [y4 [y5 [y6 [y7 [y8 [y9 [y10 [y11 [y12 [y13 [y14 [y15 B1]]]]]]]]]]]]]]]].
 destruct (listD16 _ H) as
  [z0 [z1 [z2 [z3 [z4 [z5 [z6 [z7 [z8 [z9 [z10 [z11 [z12 [z13 [z14 [z15 C1]]]]]]]]]]]]]]]].
subst xs ys l.
unfold Znth in L.
destruct (L 0) as [x [y [X [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y; inv Q.
destruct (L 1) as [x [y [X [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y; inv Q.
destruct (L 2) as [x [y [X [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y; inv Q.
destruct (L 3) as [x [y [X [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y; inv Q.
destruct (L 4) as [x [y [X [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y; inv Q.
destruct (L 5) as [x [y [X [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y; inv Q.
destruct (L 6) as [x [y [X [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y; inv Q.
destruct (L 7) as [x [y [X [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y; inv Q.
destruct (L 8) as [x [y [X [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y; inv Q.
destruct (L 9) as [x [y [X [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y; inv Q.
destruct (L 10) as [x [y [X [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y; inv Q.
destruct (L 11) as [x [y [X [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y; inv Q.
destruct (L 12) as [x [y [X [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y; inv Q.
destruct (L 13) as [x [y [X [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y; inv Q.
destruct (L 14) as [x [y [X [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y; inv Q.
destruct (L 15) as [x [y [X [Y Q]]]]; try omega.
simpl in X, Y, Q. symmetry in X, Y; inv X; inv Y; inv Q. reflexivity.
Qed.

Definition fcore_EpiloguePOST t y x w nonce out c k h OUT
  (data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte)) :=
match data with ((Nonce, C), K) =>
EX xs:_, EX ys:_,
PROP (ys = prepare_data data /\ Snuffle 20 ys = Some xs)
LOCAL (lvar _t (tarray tuint 4) t;
       lvar _y (tarray tuint 16) y; lvar _x (tarray tuint 16) x;
       lvar _w (tarray tuint 16) w; temp _in nonce; temp _out out; temp _c c;
       temp _k k; temp _h (Vint (Int.repr h)))
  SEP (CoreInSEP data (nonce, c, k);
       data_at Tsh (tarray tuint 16) (map Vint ys) y;
       data_at_ Tsh (tarray tuint 4) t; data_at_ Tsh (tarray tuint 16) w;
       if Int.eq (Int.repr h) Int.zero
         then EX l:_,
          !!HFalse_inv l 16 xs ys &&
          (data_at Tsh (tarray tuchar 64) l out *
           data_at Tsh (tarray tuint 16) (map Vint xs) x)
         else EX intsums:_, !!(HTrue_inv intsums xs ys) &&
            (data_at Tsh (tarray tuchar 32)
               (hPosLoop3 4 (hPosLoop2 4 intsums C Nonce) OUT) out
             * data_at Tsh (tarray tuint 16)
                 (map Vint (hPosLoop2 4 intsums C Nonce)) x))
end. 

Opaque Snuffle. Opaque hPosLoop2. Opaque hPosLoop3. 

Lemma HTruePOST F t y x w nonce out c k h snuffleRes l data OUT:
      Snuffle 20 l = Some snuffleRes ->
      Int.eq (Int.repr h) Int.zero = false ->
      l = prepare_data data ->
      F |-- data_at_ Tsh (tarray tuint 4) t * data_at_ Tsh (tarray tuint 16) w ->
      HTruePostCond F t y x w nonce out c k h snuffleRes l data OUT
|-- fcore_EpiloguePOST t y x w nonce out c k h OUT data.
Proof. intros.
unfold HTruePostCond, fcore_EpiloguePOST.
destruct data as [[? ?] [? ?]].
Exists snuffleRes l.
rewrite H0, <- H1, H. clear - H2.
Time normalize. (*1.4*)
 Exists intsums.
 go_lowerx. (* must do this explicitly because it's not an ENTAIL *)
 Time entailer!; auto. (*6.8*)
Qed.

Lemma HFalsePOST F t y x w nonce out c k h snuffleRes l data OUT:
      Snuffle 20 l = Some snuffleRes ->
      Int.eq (Int.repr h) Int.zero = true ->
      l = prepare_data data ->
      F |-- (CoreInSEP data (nonce, c,k) * data_at_ Tsh (tarray tuint 4) t *
             data_at_ Tsh (tarray tuint 16) w) ->
      HFalsePostCond F t y x w nonce out c k h snuffleRes l
     |-- fcore_EpiloguePOST t y x w nonce out c k h OUT data.
Proof. intros.
unfold HFalsePostCond, fcore_EpiloguePOST.
destruct data as [[? ?] [? ?]].
Exists snuffleRes l.
rewrite H0, <- H1, H. clear - H2.
go_lowerx. (* must do this explicitly because it's not an ENTAIL *)
Time entailer!. (*3.4*)
Intros intsums. Exists intsums; entailer!. apply H2.
Qed.

Opaque HTruePostCond. Opaque HFalsePostCond.

Lemma core_spec_ok: semax_body SalsaVarSpecs SalsaFunSpecs
       f_core core_spec.
Proof. unfold core_spec, f_core_POST.
start_function. abbreviate_semax.
rename v_t into t.
rename v_y into y.
rename v_x into x.
rename v_w into w.
freeze [0;1;2;3;4] FR1.
Time assert_PROP (Zlength OUT = Z.max 0 (OutLen h)) as ZL_OUT by entailer!.
rewrite Z.max_r in ZL_OUT.
2:{ unfold OutLen. simple_if_tac; omega. }
apply semax_seq with (Q:=fcore_EpiloguePOST t y x w nonce out c k h OUT data).
  + thaw FR1. freeze [0;1;3;5] FR2.
    forward_seq.
    apply (f_core_loop1 Espec (FRZL FR2) c k h nonce out w x y t data); trivial.

    (*/FOR(i,16) y[i] = x[i]*)
    Intros xInit. red in H. rename H into XInit.
    thaw FR2. freeze [0;2;3;5] FR3.
    forward_seq.
    apply (f_core_loop2 _ (FRZL FR3) c k h nonce out w x y t data); trivial.
    (* mkConciseDelta SalsaVarSpecs SalsaFunSpecs f_core Delta.*)

    Intros YS.
    destruct H as [? [? [? [? [? [? [? [? ?]]]]]]]].
    assert (L31: Zlength (x3 ++ x1) = 16) by (rewrite H1; reflexivity).
    rewrite Zlength_app, H3 in L31. destruct x1. 2:{ rewrite Zlength_cons', Z.add_assoc in L31. specialize (Zlength_nonneg x1); intros; omega. }
    rewrite app_nil_r in *. clear L31; subst x0. clear H3 H1 x3.
    assert (LX: Zlength xInit = 16).
      rewrite XInit. rewrite upd_upto_Zlength; trivial. simpl; omega.
    rewrite <- H0, Zlength_app, H2 in LX. destruct x2. 2:{ rewrite Zlength_cons', Z.add_assoc in LX. specialize (Zlength_nonneg x2); intros; omega. }
    rewrite app_nil_r in *. clear LX; subst YS. rename H2 into xInit_Zlength.

    rewrite upd_upto_char in XInit. 2: reflexivity.
    destruct data as [[Nonce C] [Key1 Key2]].
    destruct Nonce as [[[N1 N2] N3] N4].
    destruct C as [[[C1 C2] C3] C4].
    destruct Key1 as [[[K1 K2] K3] K4].
    destruct Key2 as [[[L1 L2] L3] L4].

    thaw FR3. subst xInit.
    freeze [2;3;5] FR4.
    remember [C1; K1; K2; K3; K4; C2; N1; N2; N3; N4; C3; L1; L2; L3; L4; C4] as xInit.
    forward_seq.
    eapply semax_post_flipped'.
    apply (f_core_loop3 _ (FRZL FR4) c k h nonce out w x y t (map littleendian xInit)).
    intros. apply andp_left2. apply derives_refl.
    Intros snuffleRes. rename H into RES.

    freeze [0;1;2;3] FR5.
    Time forward_if (fcore_EpiloguePOST t y x w nonce out c k h OUT
               ((N1, N2, N3, N4), (C1, C2, C3, C4), ((K1, K2, K3, K4), (L1, L2, L3, L4)))). (*4.8*)
    - (*apply typed_true_tint_Vint in H.*)
      assert (HOUTLEN: OutLen h = 32). unfold OutLen. rewrite Int.eq_false; trivial.
      thaw FR5. thaw FR4. rewrite HOUTLEN in *. freeze [3;4] FR6.
      force_sequential.
      eapply semax_post_flipped'.
      eapply (verif_fcore_epilogue_htrue Espec (FRZL FR6) t y x w nonce out c k h
                     OUT snuffleRes (map littleendian xInit)
                     (((N1, N2, N3, N4), (C1, C2, C3, C4)), (K1, K2, K3, K4, (L1, L2, L3, L4)))).
        apply andp_left2.
        apply HTruePOST; trivial. rewrite Int.eq_false; trivial.
        subst xInit; reflexivity.
        thaw FR6. cancel.
    - (*unfold typed_false in H. simpl in H. inversion H. apply negb_false_iff in H1. clear H.*)
      assert (HOUTLEN: OutLen h = 64). unfold OutLen; rewrite H; trivial.
      thaw FR5. thaw FR4. rewrite HOUTLEN in *. freeze [1;3;4] FR6.
      drop_LOCAL 0%nat.
      eapply semax_post_flipped'.
      apply (verif_fcore_epilogue_hfalse Espec (FRZL FR6)
            t y x w nonce out c k h OUT).
      apply andp_left2.
        apply HFalsePOST; trivial. rewrite H. trivial. subst; trivial.
        thaw FR6. cancel.
  + unfold fcore_EpiloguePOST.
    destruct data as [[Nonce C] [Key1 Key2]].
    abbreviate_semax.
    Intros snuffleRes ys.
    freeze [0;1;2;3;4] FR2.
    Time forward. (*4 versus 18*)
    thaw FR2. Time entailer!. (*4.6 versus 8.4*)
    rewrite Zlength_map in H1.
    specialize (Snuffle_length _ _ _  H0 (prepare_data_length _ )); intros L.
    unfold fcore_result.
    unfold Snuffle20, bind. rewrite H0; clear H0.
    remember (Int.eq (Int.repr h) Int.zero) as hh.
    destruct hh.
    - Intros l. Exists l.
        destruct (HFalse_inv16_char _ _ _ H0) as [sums [SUMS1 SUMS2]].
          rewrite Zlength_correct, L; reflexivity. trivial.
        rewrite <- SUMS1, <- SUMS2.
        unfold fcorePOST_SEP, OutLen. rewrite <- Heqhh.
        Time entailer!. (*1.7*)
    - Intros intsums.
      Exists (hPosLoop3 4 (hPosLoop2 4 intsums C Nonce) OUT).
      apply HTrue_inv_char in H0. rewrite <- H0.
      destruct Nonce as [[[? ?] ?] ?]. destruct C as [[[? ?] ?] ?].
      rewrite <- TP with (OUT:=OUT).
      unfold fcorePOST_SEP, OutLen. rewrite <- Heqhh.
      Time entailer!. (*4.3*)
       rewrite Zlength_correct, (sumlist_length _ _ _ H0), prepare_data_length; trivial.
        rewrite ZL_OUT. unfold OutLen; rewrite <- Heqhh. trivial.
        rewrite Zlength_correct, L; reflexivity.
        rewrite Zlength_correct, prepare_data_length; reflexivity.
Time Qed. (*20 versus 58*)