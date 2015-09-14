(* Functional implementation of Salsa20 whose
   structure matches the one of tweetnacl.c implementation,
   plus proof of coorrectness wrt Salsa20.v

   Lennart Beringer, June 2015*)
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
Require Import Snuffle. 
Require Import spec_salsa.

Require Import verif_fcore_loop1.
Require Import verif_fcore_loop2.
Require Import verif_fcore_loop3.

Require Import verif_fcore_epilogue_htrue.
Require Import verif_fcore_epilogue_hfalse.

Opaque littleendian_invert. Opaque Snuffle.Snuffle.
Opaque core_spec. Opaque ld32_spec. Opaque L32_spec. Opaque st32_spec.
Opaque crypto_core_salsa20_spec. Opaque crypto_core_hsalsa20_spec.

Lemma HFalse_inv16_char: forall l xs ys,
  HFalse_inv l 16 xs ys ->
  length xs = 16%nat -> length ys=16%nat ->
  exists sum, Some sum = sumlist xs ys /\ 
  l = QuadChunks2ValList (map littleendian_invert sum).
Proof. intros. destruct H.
destruct l; simpl in H. omega. rename v into v0. 
destruct l; simpl in H. omega. rename v into v1. 
destruct l; simpl in H. omega. rename v into v2. 
destruct l; simpl in H. omega. rename v into v3. 
destruct l; simpl in H. omega. rename v into v4. 
destruct l; simpl in H. omega. rename v into v5. 
destruct l; simpl in H. omega. rename v into v6. 
destruct l; simpl in H. omega. rename v into v7. 
destruct l; simpl in H. omega. rename v into v8. 
destruct l; simpl in H. omega. rename v into v9. 
destruct l; simpl in H. omega. rename v into v10. 
destruct l; simpl in H. omega. rename v into v11. 
destruct l; simpl in H. omega. rename v into v12. 
destruct l; simpl in H. omega. rename v into v13. 
destruct l; simpl in H. omega. rename v into v14. 
destruct l; simpl in H. omega. rename v into v15. 
destruct l; simpl in H. omega. rename v into v16. 
destruct l; simpl in H. omega. rename v into v17. 
destruct l; simpl in H. omega. rename v into v18. 
destruct l; simpl in H. omega. rename v into v19. 
destruct l; simpl in H. omega. rename v into v20. 
destruct l; simpl in H. omega. rename v into v21. 
destruct l; simpl in H. omega. rename v into v22. 
destruct l; simpl in H. omega. rename v into v23. 
destruct l; simpl in H. omega. rename v into v24. 
destruct l; simpl in H. omega. rename v into v25. 
destruct l; simpl in H. omega. rename v into v26. 
destruct l; simpl in H. omega. rename v into v27. 
destruct l; simpl in H. omega. rename v into v28. 
destruct l; simpl in H. omega. rename v into v29. 
destruct l; simpl in H. omega. rename v into v30. 
destruct l; simpl in H. omega. rename v into v31. 
destruct l; simpl in H. omega. rename v into v32. 
destruct l; simpl in H. omega. rename v into v33. 
destruct l; simpl in H. omega. rename v into v34. 
destruct l; simpl in H. omega. rename v into v35. 
destruct l; simpl in H. omega. rename v into v36. 
destruct l; simpl in H. omega. rename v into v37. 
destruct l; simpl in H. omega. rename v into v38. 
destruct l; simpl in H. omega. rename v into v39. 
destruct l; simpl in H. omega. rename v into v40. 
destruct l; simpl in H. omega. rename v into v41. 
destruct l; simpl in H. omega. rename v into v42. 
destruct l; simpl in H. omega. rename v into v43. 
destruct l; simpl in H. omega. rename v into v44. 
destruct l; simpl in H. omega. rename v into v45. 
destruct l; simpl in H. omega. rename v into v46. 
destruct l; simpl in H. omega. rename v into v47. 
destruct l; simpl in H. omega. rename v into v48. 
destruct l; simpl in H. omega. rename v into v49. 
destruct l; simpl in H. omega. rename v into v50. 
destruct l; simpl in H. omega. rename v into v51. 
destruct l; simpl in H. omega. rename v into v52. 
destruct l; simpl in H. omega. rename v into v53. 
destruct l; simpl in H. omega. rename v into v54. 
destruct l; simpl in H. omega. rename v into v55. 
destruct l; simpl in H. omega. rename v into v56. 
destruct l; simpl in H. omega. rename v into v57. 
destruct l; simpl in H. omega. rename v into v58. 
destruct l; simpl in H. omega. rename v into v59. 
destruct l; simpl in H. omega. rename v into v60. 
destruct l; simpl in H. omega. rename v into v61. 
destruct l; simpl in H. omega. rename v into v62. 
destruct l; simpl in H. omega. rename v into v63. 
destruct l; simpl in H. 2: omega. clear H.
destruct xs; simpl in H0. omega. rename i into x0. 
destruct xs; simpl in H0. omega. rename i into x1. 
destruct xs; simpl in H0. omega. rename i into x2. 
destruct xs; simpl in H0. omega. rename i into x3. 
destruct xs; simpl in H0. omega. rename i into x4. 
destruct xs; simpl in H0. omega. rename i into x5. 
destruct xs; simpl in H0. omega. rename i into x6. 
destruct xs; simpl in H0. omega. rename i into x7. 
destruct xs; simpl in H0. omega. rename i into x8. 
destruct xs; simpl in H0. omega. rename i into x9. 
destruct xs; simpl in H0. omega. rename i into x10. 
destruct xs; simpl in H0. omega. rename i into x11. 
destruct xs; simpl in H0. omega. rename i into x12. 
destruct xs; simpl in H0. omega. rename i into x13. 
destruct xs; simpl in H0. omega. rename i into x14. 
destruct xs; simpl in H0. omega. rename i into x15.
destruct xs; simpl in H0. 2: omega. clear H0.  
destruct ys; simpl in H1. omega. rename i into y0. 
destruct ys; simpl in H1. omega. rename i into y1. 
destruct ys; simpl in H1. omega. rename i into y2. 
destruct ys; simpl in H1. omega. rename i into y3. 
destruct ys; simpl in H1. omega. rename i into y4. 
destruct ys; simpl in H1. omega. rename i into y5. 
destruct ys; simpl in H1. omega. rename i into y6. 
destruct ys; simpl in H1. omega. rename i into y7. 
destruct ys; simpl in H1. omega. rename i into y8. 
destruct ys; simpl in H1. omega. rename i into y9. 
destruct ys; simpl in H1. omega. rename i into y10. 
destruct ys; simpl in H1. omega. rename i into y11. 
destruct ys; simpl in H1. omega. rename i into y12. 
destruct ys; simpl in H1. omega. rename i into y13. 
destruct ys; simpl in H1. omega. rename i into y14. 
destruct ys; simpl in H1. omega. rename i into y15. 
destruct ys; simpl in H1. 2: omega. clear H1.
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
(*
Lemma TP C1 C2 C3 C4 N1 N2 N3 N4 intsums OUT: length intsums = 16%nat -> length OUT = 64%nat ->
  hPosLoop3 4 (hPosLoop2 4 intsums (C1, C2, C3, C4) (N1, N2, N3, N4)) OUT = 
 QuadByte2ValList (littlendian_invert (Int.sub (Znth 0 intsums Int.zero)  (littleendian C1))) ++
 QuadByte2ValList (littlendian_invert (Int.sub (Znth 5 intsums Int.zero)  (littleendian C2))) ++
 QuadByte2ValList (littlendian_invert (Int.sub (Znth 10 intsums Int.zero) (littleendian C3))) ++
 QuadByte2ValList (littlendian_invert (Int.sub (Znth 15 intsums Int.zero) (littleendian C4))) ++
 QuadByte2ValList (littlendian_invert (Int.sub (Znth 6 intsums Int.zero)  (littleendian N1))) ++
 QuadByte2ValList (littlendian_invert (Int.sub (Znth 7 intsums Int.zero)  (littleendian N2))) ++
 QuadByte2ValList (littlendian_invert (Int.sub (Znth 8 intsums Int.zero)  (littleendian N3))) ++
 QuadByte2ValList (littlendian_invert (Int.sub (Znth 9 intsums Int.zero)  (littleendian N4))) ++
 skipn 32 OUT.
Proof. intros.
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
destruct OUT; simpl in H0. omega. rename v into u32. 
destruct OUT; simpl in H0. omega. rename v into u33. 
destruct OUT; simpl in H0. omega. rename v into u34. 
destruct OUT; simpl in H0. omega. rename v into u35. 
destruct OUT; simpl in H0. omega. rename v into u36. 
destruct OUT; simpl in H0. omega. rename v into u37. 
destruct OUT; simpl in H0. omega. rename v into u38. 
destruct OUT; simpl in H0. omega. rename v into u39. 
destruct OUT; simpl in H0. omega. rename v into u40. 
destruct OUT; simpl in H0. omega. rename v into u41. 
destruct OUT; simpl in H0. omega. rename v into u42. 
destruct OUT; simpl in H0. omega. rename v into u43. 
destruct OUT; simpl in H0. omega. rename v into u44. 
destruct OUT; simpl in H0. omega. rename v into u45. 
destruct OUT; simpl in H0. omega. rename v into u46. 
destruct OUT; simpl in H0. omega. rename v into u47. 
destruct OUT; simpl in H0. omega. rename v into u48. 
destruct OUT; simpl in H0. omega. rename v into u49. 
destruct OUT; simpl in H0. omega. rename v into u50. 
destruct OUT; simpl in H0. omega. rename v into u51. 
destruct OUT; simpl in H0. omega. rename v into u52. 
destruct OUT; simpl in H0. omega. rename v into u53. 
destruct OUT; simpl in H0. omega. rename v into u54. 
destruct OUT; simpl in H0. omega. rename v into u55. 
destruct OUT; simpl in H0. omega. rename v into u56. 
destruct OUT; simpl in H0. omega. rename v into u57. 
destruct OUT; simpl in H0. omega. rename v into u58. 
destruct OUT; simpl in H0. omega. rename v into u59. 
destruct OUT; simpl in H0. omega. rename v into u60. 
destruct OUT; simpl in H0. omega. rename v into u61. 
destruct OUT; simpl in H0. omega. rename v into u62. 
destruct OUT; simpl in H0. omega. rename v into u63. 
destruct OUT; simpl in H0. 2: omega. clear H0. simpl. reflexivity.
Qed.*)

Opaque firstn.

Lemma TP1 C1 C2 C3 C4 N1 N2 N3 N4 intsums OUT: length intsums = 16%nat -> length OUT = 64%nat ->
 firstn 32 (hPosLoop3 4 (hPosLoop2 4 intsums (C1, C2, C3, C4) (N1, N2, N3, N4)) OUT) = 
 QuadByte2ValList (littleendian_invert (Int.sub (Znth 0 intsums Int.zero)  (littleendian C1))) ++
 QuadByte2ValList (littleendian_invert (Int.sub (Znth 5 intsums Int.zero)  (littleendian C2))) ++
 QuadByte2ValList (littleendian_invert (Int.sub (Znth 10 intsums Int.zero) (littleendian C3))) ++
 QuadByte2ValList (littleendian_invert (Int.sub (Znth 15 intsums Int.zero) (littleendian C4))) ++
 QuadByte2ValList (littleendian_invert (Int.sub (Znth 6 intsums Int.zero)  (littleendian N1))) ++
 QuadByte2ValList (littleendian_invert (Int.sub (Znth 7 intsums Int.zero)  (littleendian N2))) ++
 QuadByte2ValList (littleendian_invert (Int.sub (Znth 8 intsums Int.zero)  (littleendian N3))) ++
 QuadByte2ValList (littleendian_invert (Int.sub (Znth 9 intsums Int.zero)  (littleendian N4))).
Proof. intros.
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
destruct OUT; simpl in H0. omega. rename v into u32. 
destruct OUT; simpl in H0. omega. rename v into u33. 
destruct OUT; simpl in H0. omega. rename v into u34. 
destruct OUT; simpl in H0. omega. rename v into u35. 
destruct OUT; simpl in H0. omega. rename v into u36. 
destruct OUT; simpl in H0. omega. rename v into u37. 
destruct OUT; simpl in H0. omega. rename v into u38. 
destruct OUT; simpl in H0. omega. rename v into u39. 
destruct OUT; simpl in H0. omega. rename v into u40. 
destruct OUT; simpl in H0. omega. rename v into u41. 
destruct OUT; simpl in H0. omega. rename v into u42. 
destruct OUT; simpl in H0. omega. rename v into u43. 
destruct OUT; simpl in H0. omega. rename v into u44. 
destruct OUT; simpl in H0. omega. rename v into u45. 
destruct OUT; simpl in H0. omega. rename v into u46. 
destruct OUT; simpl in H0. omega. rename v into u47. 
destruct OUT; simpl in H0. omega. rename v into u48. 
destruct OUT; simpl in H0. omega. rename v into u49. 
destruct OUT; simpl in H0. omega. rename v into u50. 
destruct OUT; simpl in H0. omega. rename v into u51. 
destruct OUT; simpl in H0. omega. rename v into u52. 
destruct OUT; simpl in H0. omega. rename v into u53. 
destruct OUT; simpl in H0. omega. rename v into u54. 
destruct OUT; simpl in H0. omega. rename v into u55. 
destruct OUT; simpl in H0. omega. rename v into u56. 
destruct OUT; simpl in H0. omega. rename v into u57. 
destruct OUT; simpl in H0. omega. rename v into u58. 
destruct OUT; simpl in H0. omega. rename v into u59. 
destruct OUT; simpl in H0. omega. rename v into u60. 
destruct OUT; simpl in H0. omega. rename v into u61. 
destruct OUT; simpl in H0. omega. rename v into u62. 
destruct OUT; simpl in H0. omega. rename v into u63. 
destruct OUT; simpl in H0. 2: omega. clear H0. simpl. reflexivity.
Qed.

Definition HTrue_inv intsums xs ys:Prop:=
Zlength intsums = 16 /\
        (forall j, 0 <= j < 16 -> 
           exists xj, exists yj, 
           Znth j (map Vint xs) Vundef = Vint xj /\
           Znth j (map Vint ys) Vundef = Vint yj /\
           Znth j (map Vint intsums) Vundef = Vint (Int.add yj xj)).

Lemma HTrue_inv_char l xs ys: length xs = 16%nat -> length ys=16%nat ->
      HTrue_inv l xs ys -> Some l = sumlist xs ys.
Proof. rewrite sumlist_symm. intros LX LY [H L].
apply hmac_pure_lemmas.Zlength_length in H; simpl in H. 2: omega.
destruct l; simpl in H. omega. rename i into v0. 
destruct l; simpl in H. omega. rename i into v1. 
destruct l; simpl in H. omega. rename i into v2. 
destruct l; simpl in H. omega. rename i into v3. 
destruct l; simpl in H. omega. rename i into v4. 
destruct l; simpl in H. omega. rename i into v5. 
destruct l; simpl in H. omega. rename i into v6. 
destruct l; simpl in H. omega. rename i into v7. 
destruct l; simpl in H. omega. rename i into v8. 
destruct l; simpl in H. omega. rename i into v9. 
destruct l; simpl in H. omega. rename i into v10. 
destruct l; simpl in H. omega. rename i into v11. 
destruct l; simpl in H. omega. rename i into v12. 
destruct l; simpl in H. omega. rename i into v13. 
destruct l; simpl in H. omega. rename i into v14. 
destruct l; simpl in H. omega. rename i into v15. 
destruct l; simpl in H. 2: omega. clear H.
destruct xs; simpl in LX. omega. rename i into x0. 
destruct xs; simpl in LX. omega. rename i into x1. 
destruct xs; simpl in LX. omega. rename i into x2. 
destruct xs; simpl in LX. omega. rename i into x3. 
destruct xs; simpl in LX. omega. rename i into x4. 
destruct xs; simpl in LX. omega. rename i into x5. 
destruct xs; simpl in LX. omega. rename i into x6. 
destruct xs; simpl in LX. omega. rename i into x7. 
destruct xs; simpl in LX. omega. rename i into x8. 
destruct xs; simpl in LX. omega. rename i into x9. 
destruct xs; simpl in LX. omega. rename i into x10. 
destruct xs; simpl in LX. omega. rename i into x11. 
destruct xs; simpl in LX. omega. rename i into x12. 
destruct xs; simpl in LX. omega. rename i into x13. 
destruct xs; simpl in LX. omega. rename i into x14. 
destruct xs; simpl in LX. omega. rename i into x15.
destruct xs; simpl in LX. 2: omega. clear LX.  
destruct ys; simpl in LY. omega. rename i into y0. 
destruct ys; simpl in LY. omega. rename i into y1. 
destruct ys; simpl in LY. omega. rename i into y2. 
destruct ys; simpl in LY. omega. rename i into y3. 
destruct ys; simpl in LY. omega. rename i into y4. 
destruct ys; simpl in LY. omega. rename i into y5. 
destruct ys; simpl in LY. omega. rename i into y6. 
destruct ys; simpl in LY. omega. rename i into y7. 
destruct ys; simpl in LY. omega. rename i into y8. 
destruct ys; simpl in LY. omega. rename i into y9. 
destruct ys; simpl in LY. omega. rename i into y10. 
destruct ys; simpl in LY. omega. rename i into y11. 
destruct ys; simpl in LY. omega. rename i into y12. 
destruct ys; simpl in LY. omega. rename i into y13. 
destruct ys; simpl in LY. omega. rename i into y14. 
destruct ys; simpl in LY. omega. rename i into y15. 
destruct ys; simpl in LY. 2: omega. clear LY.
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
  SEP (`(SByte Nonce nonce); `(SByte C c);
       `(ThirtyTwoByte K k);
       `(data_at Tsh (tarray tuint 16) (map Vint ys) y);
       `(data_at_ Tsh (tarray tuint 4) t); `(data_at_ Tsh (tarray tuint 16) w);
       `(if Int.eq (Int.repr h) Int.zero 
         then EX l:_, 
          !!HFalse_inv l 16 xs ys && 
          (data_at Tsh (tarray tuchar 64) l out *
           data_at Tsh (tarray tuint 16) (map Vint xs) x)
         else EX intsums:_, !!(HTrue_inv intsums xs ys) && 
            (data_at Tsh (tarray tuchar 64)
               (hPosLoop3 4 (hPosLoop2 4 intsums C Nonce) OUT) out
             * data_at Tsh (tarray tuint 16)
                 (map Vint (hPosLoop2 4 intsums C Nonce)) x)))
end.

Opaque HTruePostCond. Opaque HFalsePostCond. Opaque Snuffle.
Opaque hPosLoop2. Opaque hPosLoop3. Opaque ThirtyTwoByte.

Lemma core_spec_ok: semax_body SalsaVarSpecs SalsaFunSpecs
       f_core core_spec.
Proof. Transparent core_spec. unfold core_spec, f_core_POST. Opaque core_spec. 
start_function.
name out' _out.
name in' _in.
name k' _k.
name c' _c.
name h' _h.
name aux' _aux.
simpl_stackframe_of. 
fixup_local_var. intro w.
fixup_local_var. intro x.
fixup_local_var. intro y.
fixup_local_var. intro t.
normalize. rename H into OUTlen.

apply semax_seq with (Q:=fcore_EpiloguePOST t y x w nonce out c k h OUT data).
(*forward_seq.*)
  { forward_seq. apply f_core_loop1; trivial. 
 
  (* continuation after first loop*) 

  (*/FOR(i,16) y[i] = x[i]*)
  normalize. intros xInit. normalize. rename H into XInit.
  destruct XInit as [n [? XInit]]. 
  assert (ZZ: Z.to_nat 4 = Z.to_nat (Z.of_nat n)) by (rewrite <- H; trivial). 
  rewrite Nat2Z.id in ZZ. clear H; subst n.
  forward_seq. apply f_core_loop2; trivial.
  (* mkConciseDelta SalsaVarSpecs SalsaFunSpecs f_core Delta.*)

  normalize. intros YS; normalize.
  destruct H as [n [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
  assert (N: n=16%nat). specialize (Nat2Z.id n). rewrite <- H. intros Q; rewrite <- Q; reflexivity. 
  rewrite N in *; clear N H.
  assert (length (x3 ++ x1) = 16%nat) by (rewrite H2; reflexivity).
  rewrite app_length, H4 in H. destruct x1; simpl in H; try omega. rewrite app_nil_r in H0; clear H; subst x0.
  clear H2 H4.
  assert (LX: length xInit = 16%nat).
     rewrite XInit. rewrite upd_upto_length; trivial. simpl; omega.
   rewrite <- H1, app_length, H3 in LX. destruct x2; simpl in LX; try omega.
   rewrite app_nil_r in H1; subst YS. clear LX x3 n. rename H3 into xInit_length.

  rewrite upd_upto_char in XInit. 2: reflexivity.
  destruct data as [[Nonce C] [Key1 Key2]]. 
   destruct Nonce as [[[N1 N2] N3] N4].
   destruct C as [[[C1 C2] C3] C4].
   destruct Key1 as [[[K1 K2] K3] K4].
   destruct Key2 as [[[L1 L2] L3] L4]. subst xInit.
  forward_seq. apply f_core_loop3; trivial. 
  remember [C1; K1; K2; K3; K4; C2; N1; N2; N3; N4; C3; L1; L2; L3; L4; C4] as xInit.
  normalize. intros snuffleRes. normalize. rename H into RES.

  forward_if (fcore_EpiloguePOST t y x w nonce out c k h OUT 
   ((N1, N2, N3, N4), (C1, C2, C3, C4), ((K1, K2, K3, K4), (L1, L2, L3, L4)))).
  (*mkConciseDelta SalsaVarSpecs SalsaFunSpecs f_core Delta.*)
  { eapply semax_pre_post.
    Focus 3. eapply (verif_fcore_epilogue_htrue Espec t y x w nonce out c k h 
                     OUT snuffleRes (map littleendian xInit)
                     (N1, N2, N3, N4) (C1, C2, C3, C4) (K1, K2, K3, K4, (L1, L2, L3, L4))).
    erewrite Zlength_correct, Snuffle_length. trivial. eassumption. subst xInit; trivial.
    subst xInit; trivial.
    rewrite Zlength_correct, OUTlen; reflexivity. 
    entailer.
    simpl. intros. 
    unfold typed_true in H. simpl in H. inv H. apply negb_true_iff in H1. rewrite H1.
    unfold overridePost, POSTCONDITION, abbreviate, normal_ret_assert.
    normalize. clear H. simpl. Transparent HTruePostCond. unfold HTruePostCond. Opaque HTruePostCond. 
    apply (exp_right snuffleRes).
    apply (exp_right (map littleendian [C1; K1; K2; K3; K4; C2; N1; N2;
         N3; N4; C3; L1; L2; L3; L4; C4])).
    (*unfold HTrue_inv.*) entailer.
    apply (exp_right x1). apply andp_right. apply prop_right. trivial. 
    entailer. apply andp_right. apply prop_right. split; assumption.
    cancel. } 

  { eapply semax_pre_post.
    Focus 3. eapply (verif_fcore_epilogue_hfalse Espec t y x w nonce out c k h 
                     (N1, N2, N3, N4, (C1, C2, C3, C4), (K1, K2, K3, K4, (L1, L2, L3, L4)))
                     OUT snuffleRes (map littleendian xInit)).
    erewrite Zlength_correct, Snuffle_length. trivial. eassumption. subst xInit; trivial.
    subst xInit; trivial.
    assumption.
    entailer.
    simpl. intros. 
    unfold typed_false in H. simpl in H. inv H. apply negb_false_iff in H1. rewrite H1. 
    unfold overridePost, POSTCONDITION, abbreviate, normal_ret_assert.
    normalize. clear H. simpl. Transparent HFalsePostCond. unfold HFalsePostCond. Opaque HTruePostCond. 
    apply (exp_right snuffleRes).
    apply (exp_right (map littleendian [C1; K1; K2; K3; K4; C2; N1; N2;
         N3; N4; C3; L1; L2; L3; L4; C4])).
    entailer.
    apply (exp_right x1). entailer. cancel. } 

  { simpl; intros. entailer. clear H.
    unfold POSTCONDITION, abbreviate, fcore_EpiloguePOST, overridePost.
    destruct (eq_dec ek EK_normal); apply derives_refl. }
}
normalize. unfold fcore_EpiloguePOST.
destruct data as [[Nonce C] [Key1 Key2]]. 
   destruct Nonce as [[[N1 N2] N3] N4].
   destruct C as [[[C1 C2] C3] C4].
   destruct Key1 as [[[K1 K2] K3] K4].
   destruct Key2 as [[[L1 L2] L3] L4]. 
apply extract_exists_pre; intros snuffleRes.
apply extract_exists_pre; intros ys.
unfold MORE_COMMANDS, abbreviate. (*WHY's THAT NEEDED?*) forward.
unfold fcorePOST_SEP. 
specialize (Snuffle_length _ _ _ H0 (eq_refl _)); intros L.
unfold fcore_result. 
destruct (Int.eq (Int.repr h) Int.zero).
{ normalize. apply (exp_right l).
  destruct (HFalse_inv16_char _ _ _ H8 L (eq_refl _)) as [sums [SUMS1 SUMS2]].
  entailer.
  apply andp_right. apply prop_right.
    unfold Snuffle20, prepare_data. simpl; rewrite H0.
    simpl. rewrite <- SUMS1. trivial.
  simpl_stackframe_of. normalize.
  rewrite (lvar_eval_lvar _ _ _ _ H1). rewrite (lvar_eval_lvar _ _ _ _ H2).
  rewrite (lvar_eval_lvar _ _ _ _ H3). rewrite (lvar_eval_lvar _ _ _ _ H4).
  unfold CoreInSEP. cancel. }
{ normalize.
  apply (exp_right (hPosLoop3 4 (hPosLoop2 4 intsums (C1, C2, C3, C4) (N1, N2, N3, N4)) OUT)).
  entailer.
  apply andp_right. apply prop_right. 
    unfold Snuffle20, prepare_data. simpl; rewrite H0.
    simpl. 
    apply HTrue_inv_char in H8. rewrite <- H8. apply TP1.
    rewrite (sumlist_length _ _ _ H8). reflexivity.
    assumption.
    assumption. 
    reflexivity.  
  unfold CoreInSEP. cancel. 
  simpl_stackframe_of. normalize.
  rewrite (lvar_eval_lvar _ _ _ _ H1). rewrite (lvar_eval_lvar _ _ _ _ H2).
  rewrite (lvar_eval_lvar _ _ _ _ H3). rewrite (lvar_eval_lvar _ _ _ _ H4). cancel. }
Qed.
