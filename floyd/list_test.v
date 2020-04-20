Require Import VST.floyd.proofauto.
Require Import Coq.Program.Tactics.

Example strcat_preloop2_new : forall {cs : compspecs} n ld,
  n > Zlength ld ->
  data_subsume (tarray tschar n)
    (map Vbyte (ld ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + 1))) Vundef)
    (map Vbyte ld ++ list_repeat (Z.to_nat (n - Zlength ld)) Vundef).
Proof.
  intros.
  list_form. apply_list_ext. Znth_solve.
Qed.

Lemma split_data_at_app_tschar:
 forall {cs : compspecs} sh n (al bl: list val) p ,
   n = Zlength (al++bl) ->
   data_at sh (tarray tschar n) (al++bl) p = 
         data_at sh (tarray tschar (Zlength al)) al p
        * data_at sh (tarray tschar (n - Zlength al)) bl
                 (field_address0 (tarray tschar n) [ArraySubsc (Zlength al)] p).
Proof.
  intros.
  apply (split2_data_at_Tarray_app _ n  sh tschar al bl ); auto.
  rewrite Zlength_app in H.
  change ( Zlength bl = n - Zlength al); omega.
Qed.

Example strcat_preloop2_old : forall {cs : compspecs} n ld,
  n > Zlength ld ->
  data_subsume (tarray tschar n)
    (map Vbyte (ld ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + 1))) Vundef)
    (map Vbyte ld ++ list_repeat (Z.to_nat (n - Zlength ld)) Vundef).
Proof.
  unfold data_subsume; intros.
  autorewrite with sublist.
  rewrite !map_app. rewrite <- app_assoc.
  rewrite split_data_at_app_tschar by list_solve.
  rewrite (split_data_at_app_tschar _ n) by list_solve.
  autorewrite with sublist.
  cancel.
Qed.

Example strcat_retutn_new : forall n (ld ls : list byte),
  Zlength ld + Zlength ls < n ->
  map Vbyte (ld ++ ls) ++
  upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls))) Vundef) (Vint (Int.repr (Byte.signed (Znth 0 [Byte.zero])))) =
  map Vbyte ((ld ++ ls) ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls + 1))) Vundef.
Proof.
  intros.
  list_form. apply_list_ext. Znth_solve.
Qed.

(* Example using list_deduce *)
(*
Example strcat_retutn_alt : forall n (ld ls : list byte),
  Zlength ld + Zlength ls < n ->
  map Vbyte (ld ++ ls) ++
  upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls))) Vundef) (Vint (Int.repr (Byte.signed (Znth 0 [Byte.zero])))) =
  map Vbyte ((ld ++ ls) ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls + 1))) Vundef.
Proof.
  intros. list_normalize. repeat list_deduce. f_equal. Zlength_solve.
Qed.
*)

Example strcat_return_old : forall n (ld ls : list byte),
  Zlength ld + Zlength ls < n ->
  map Vbyte (ld ++ ls) ++
  upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls))) Vundef) (Vint (Int.repr (Byte.signed (Znth 0 [Byte.zero])))) =
  map Vbyte ((ld ++ ls) ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls + 1))) Vundef.
Proof.
  intros.
  replace (n - (Zlength ld + Zlength ls))
    with (1 + (n - (Zlength ld + Zlength ls+1))) by rep_omega.
  rewrite <- list_repeat_app' by rep_omega.
  rewrite upd_Znth_app1 by list_solve.
  rewrite app_assoc.
  simpl.
  rewrite !map_app.
  reflexivity.
Qed.

Example strcat_loop2_new : forall {cs : compspecs} sh n x ld ls dest,
  Zlength ls + Zlength ld < n ->
  0 <= x < Zlength ls ->
  data_at sh (tarray tschar n)
  (map Vbyte (ld ++ sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + x))) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero])))))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (ld ++ sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (Zlength ld + (x + 1)))) Vundef)
      dest.
Proof.
  intros.
  apply derives_refl'. f_equal.
  apply_list_ext. list_form. Znth_solve.
  fold_Vbyte. do 2 f_equal. omega.
Qed.

Example strcat_loop2_alt : forall {cs : compspecs} sh n x ld ls dest,
  Zlength ls + Zlength ld < n ->
  0 <= x < Zlength ls ->
  data_at sh (tarray tschar n)
  (map Vbyte (ld ++ sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + x))) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero])))))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (ld ++ sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (Zlength ld + (x + 1)))) Vundef)
      dest.
Proof.
  intros. fold_Vbyte.
  apply_list_ext. list_form. Znth_solve.
  apply data_subsume_refl'.
  do 2 f_equal. omega.
Qed.

Example strcat_loop2_old : forall {cs : compspecs} sh n x ld ls dest,
  Zlength ls + Zlength ld < n ->
  0 <= x < Zlength ls ->
  data_at sh (tarray tschar n)
  (map Vbyte (ld ++ sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + x))) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero])))))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (ld ++ sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (Zlength ld + (x + 1)))) Vundef)
      dest.
Proof.
  intros. rename x into j.
  rewrite (sublist_split 0 j (j+1)) by rep_omega.
  rewrite (app_assoc ld). rewrite !map_app.
  rewrite <- (app_assoc (_ ++ _)).
  rewrite (split_data_at_app_tschar _ n) by list_solve.
  rewrite (split_data_at_app_tschar _ n) by list_solve.
  replace (n - (Zlength ld + j))
    with (1 + (n - (Zlength ld + (j + 1)))) by rep_omega.
  rewrite <- list_repeat_app' by rep_omega.
  cancel.
  rewrite upd_Znth_app1 by (autorewrite with sublist; rep_omega).
  rewrite app_Znth1 by list_solve.
  rewrite sublist_len_1 by rep_omega.
  cancel.
Qed.

Example strcpy_return_new : forall {cs : compspecs} sh n ls dest,
  Zlength ls < n ->
  data_at sh (tarray tschar n)
  (map Vbyte ls ++ upd_Znth 0 (list_repeat (Z.to_nat (n - Zlength ls)) Vundef) (Vint (Int.repr (Byte.signed Byte.zero)))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (ls ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ls + 1))) Vundef) dest.
Proof.
  intros.
  list_form. apply_list_ext. Znth_solve.
Qed.

Example strcpy_return_old : forall {cs : compspecs} sh n ls dest,
  Zlength ls < n ->
  data_at sh (tarray tschar n)
  (map Vbyte ls ++ upd_Znth 0 (list_repeat (Z.to_nat (n - Zlength ls)) Vundef) (Vint (Int.repr (Byte.signed Byte.zero)))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (ls ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ls + 1))) Vundef) dest.
Proof.
  intros.
  autorewrite with sublist.
  rewrite !map_app.
  rewrite <- app_assoc.
   rewrite (split_data_at_app_tschar _ n) by list_solve.
   rewrite (split_data_at_app_tschar _ n) by list_solve.
   autorewrite with sublist.
   replace (n - Zlength ls) with (1 + (n - (Zlength ls + 1))) at 2 by list_solve.
  rewrite <- list_repeat_app' by omega.
  autorewrite with sublist.
  rewrite !split_data_at_app_tschar by list_solve.
  cancel.
Qed.

Example strcpy_loop_new : forall {cs : compspecs} sh n x ls dest,
  Zlength ls < n ->
  0 <= x < Zlength ls + 1 ->
  Znth x (ls ++ [Byte.zero]) <> Byte.zero ->
  data_at sh (tarray tschar n)
  (map Vbyte (sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - x)) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero])))))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (x + 1))) Vundef) dest.
Proof.
  intros.
  list_form. Znth_solve2.
  fold_Vbyte. apply_list_ext. Znth_solve.
  apply data_subsume_refl'. do 2 f_equal. omega.
Qed.

Example strcpy_loop_old : forall {cs : compspecs} sh n x ls dest,
  Zlength ls < n ->
  0 <= x < Zlength ls + 1 ->
  Znth x (ls ++ [Byte.zero]) <> Byte.zero ->
  ~ In Byte.zero ls ->
  data_at sh (tarray tschar n)
  (map Vbyte (sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - x)) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero])))))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (x + 1))) Vundef) dest.
Proof.
  intros. rename x into i.
  assert (i < Zlength ls) by cstring.
  rewrite (sublist_split 0 i (i+1)) by list_solve.
  rewrite !map_app. rewrite <- app_assoc.
  autorewrite with sublist.
  rewrite !(split_data_at_app_tschar _ n) by list_solve.
  autorewrite with sublist.
   replace (n - i) with (1 + (n-(i+ 1))) at 2 by list_solve.
  rewrite <- list_repeat_app' by omega.
  autorewrite with sublist.
  cancel.
  rewrite !split_data_at_app_tschar by list_solve.
  autorewrite with sublist.
  rewrite sublist_len_1 by omega.
  simpl. cancel.
Qed.

(* This is a very hard case, a lot of deductions are needed *)
(* cool automation now! *)
Example strcmp_loop_new : forall i ls1 ls2,
  ~ In Byte.zero ls1 ->
  ~ In Byte.zero ls2 ->
  0 <= i < Zlength ls1 + 1 ->
  0 <= i < Zlength ls2 + 1 ->
  (forall j : Z, 0 <= j < i -> Znth j ls1 = Znth j ls2) ->
  i <> Zlength ls1 \/ i <> Zlength ls2 ->
  Znth i (ls1 ++ [Byte.zero]) = Znth i (ls2 ++ [Byte.zero]) ->
  i + 1 < Zlength ls1 + 1 /\
  i + 1 < Zlength ls2 + 1 /\
  forall j : Z, 0 <= j < i + 1 -> Znth j ls1 = Znth j ls2.
Proof.
  intros.
  list_form. range_form.
  Time split3; intros; Znth_solve2; try omega; range_saturate; try congruence; fassumption.
  (* New version : Finished transaction in 2.253 secs (2.25u,0.s) (successful) *)
  (* Old version : Finished transaction in 1.383 secs (1.375u,0.s) (successful) *)
Qed.

Example strcmp_loop_old : forall i ls1 ls2,
  ~ In Byte.zero ls1 ->
  ~ In Byte.zero ls2 ->
  0 <= i < Zlength ls1 + 1 ->
  0 <= i < Zlength ls2 + 1 ->
  sublist 0 i ls1 = sublist 0 i ls2 ->
  i <> Zlength ls1 \/ i <> Zlength ls2 ->
  Znth i (ls1 ++ [Byte.zero]) = Znth i (ls2 ++ [Byte.zero]) ->
  (Znth i (ls1 ++ [Byte.zero]) = Byte.zero <-> i = Zlength ls1) -> (* these two are not needed as they can be derived *)
  (Znth i (ls2 ++ [Byte.zero]) = Byte.zero <-> i = Zlength ls2) -> (* it makes proof easier to put them here *)
  i + 1 < Zlength ls1 + 1 /\
  i + 1 < Zlength ls2 + 1 /\
  sublist 0 (i+1) ls1 = sublist 0 (i+1) ls2.
Proof.
  intros.
  destruct (zlt i (Zlength ls1)).
  2:{
         assert (i = Zlength ls1) by omega. subst.
         destruct H4; [congruence | ].
         assert (Zlength ls1 < Zlength ls2) by omega.
         rewrite app_Znth2 in H5 by rep_omega.
         rewrite app_Znth1 in H5 by rep_omega.
         rewrite Z.sub_diag in H5. contradiction H0.
         change (Znth 0 [Byte.zero]) with Byte.zero in H5.
         rewrite H5. apply Znth_In. omega.
   }
  destruct (zlt i (Zlength ls2)).
  2:{
         assert (i = Zlength ls2) by omega. subst.
         destruct H4; [ | congruence].
         assert (Zlength ls1 > Zlength ls2) by omega.
         rewrite app_Znth1 in H5 by rep_omega.
         rewrite app_Znth2 in H5 by rep_omega.
         rewrite Z.sub_diag in H5. contradiction H.
         change (Znth 0 [Byte.zero]) with Byte.zero in H5.
         rewrite <- H5.  apply Znth_In. omega.
   }
  rewrite (sublist_split 0 i (i+1)) by omega.
  rewrite (sublist_split 0 i (i+1)) by omega.
  f_equal; auto.
  rewrite !sublist_len_1 by omega.
  autorewrite with sublist in H5.
  split. rep_omega. split. rep_omega.
  f_equal; auto. f_equal. auto.
Qed.


