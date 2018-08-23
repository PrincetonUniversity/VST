Require Import VST.floyd.proofauto.
Require Import VST.progs.strlib.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition strchr_spec :=
 DECLARE _strchr
  WITH sh: share, str : val, s : list byte, c : byte
  PRE  [ _str OF tptr tschar, _c OF tint ]
    PROP (readable_share sh; c <> Byte.zero)
    LOCAL (temp _str str; temp _c (Vbyte c))
    SEP (cstring sh s str)
  POST [ tptr tschar ]
   EX r : val,
    PROP ((exists i, Znth i s = c /\ Forall (fun d => d<>c) (sublist 0 i s)
                     /\ r = offset_val i str)
       \/ (Forall (fun d => d<>c) s /\ r = nullval))
    LOCAL (temp ret_temp r)
    SEP (cstring sh s str).

Definition strcat_spec :=
 DECLARE _strcat
  WITH sh: share, sh': share, dest : val, sd : list byte, n : Z, src : val, ss : list byte
  PRE  [ _dest OF tptr tschar, _src OF tptr tschar ]
    PROP (writable_share sh; readable_share sh'; Zlength sd + Zlength ss < n)
    LOCAL (temp _dest dest; temp _src src)
    SEP (cstringn sh sd n dest; cstring sh' ss src)
  POST [ tptr tschar ]
    PROP ()
    LOCAL (temp ret_temp dest)
    SEP (cstringn sh (sd ++ ss) n dest; cstring sh' ss src).

Definition strcmp_spec :=
 DECLARE _strcmp
  WITH sh1: share, sh2: share, str1 : val, s1 : list byte, str2 : val, s2 : list byte
  PRE [ _str1 OF tptr tschar, _str2 OF tptr tschar ]
    PROP (readable_share sh1; readable_share sh2)
    LOCAL (temp _str1 str1; temp _str2 str2)
    SEP (cstring sh1 s1 str1; cstring sh2 s2 str2)
  POST [ tint ]
   EX i : int,
    PROP (if Int.eq_dec i Int.zero then s1 = s2 else s1 <> s2)
    LOCAL (temp ret_temp (Vint i))
    SEP (cstring sh1 s1 str1; cstring sh2 s2 str2).

Definition strcpy_spec :=
 DECLARE _strcpy
  WITH sh: share, sh': share, dest : val, n : Z, src : val, s : list byte
  PRE [ _dest OF tptr tschar, _src OF tptr tschar ]
    PROP (writable_share sh; readable_share sh'; Zlength s < n)
    LOCAL (temp _dest dest; temp _src src)
    SEP (data_at_ sh (tarray tschar n) dest; cstring sh' s src)
  POST [ tptr tschar ]
    PROP ()
    LOCAL (temp ret_temp dest)
    SEP (cstringn sh s n dest; cstring sh' s src).

Definition strlen_spec :=
 DECLARE _strlen
  WITH sh: share, s : list byte, str: val
  PRE [ _str OF tptr tschar ]
    PROP (readable_share sh)
    LOCAL (temp _str str)
    SEP (cstring sh s str)
  POST [ tptr tschar ]
    PROP ()
    LOCAL (temp ret_temp (Vptrofs (Ptrofs.repr (Zlength s))))
    SEP (cstring sh s str).

Definition Gprog : funspecs :=
         ltac:(with_library prog [ strchr_spec; strcat_spec; strcmp_spec ]).

Hint Rewrite Z.add_simpl_r Z.sub_simpl_r : norm entailer_rewrite.

Lemma body_strlen: semax_body Vprog Gprog f_strlen strlen_spec.
Proof.
start_function.
unfold cstring in *.
rename s into ls.
Intros.
forward.
forward_loop (EX i : Z,
  PROP (0 <= i < Zlength ls + 1)
  LOCAL (temp _str str; temp _i (Vptrofs (Ptrofs.repr i)))
  SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str))
 continue: (EX i : Z,
  PROP (0 <= i < Zlength ls + 1)
  LOCAL (temp _str str; temp _i (Vptrofs (Ptrofs.repr (i-1))))
  SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str)).
*
Exists 0. entailer!.
*
Intros i.
assert (Zlength (ls ++ [Byte.zero]) = Zlength ls + 1) by (autorewrite with sublist; auto).
forward.
forward_if.
forward.
entailer!. f_equal. f_equal. cstring.
forward. 
Exists (i+1).
entailer!. cstring.
*
Intros i.
forward.
Exists i.
entailer!.
Qed.

Lemma body_strchr: semax_body Vprog Gprog f_strchr strchr_spec.
Proof.
start_function.
forward.
unfold cstring in *.
rename s into ls.
Intros.
forward_loop (EX i : Z,
  PROP (0 <= i < Zlength ls + 1; Forall (fun d => d <> c) (sublist 0 i ls))
  LOCAL (temp _str str; temp _c (Vbyte c); temp _i (Vint (Int.repr i)))
  SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str))
 continue: (EX i : Z,
  PROP (0 <= i < Zlength ls + 1; Forall (fun d => d <> c) (sublist 0 i ls))
  LOCAL (temp _str str; temp _c (Vbyte c); temp _i (Vint (Int.repr (i-1))))
  SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str)).
  Exists 0; rewrite sublist_nil; entailer!.
- Intros i. 
  assert (Zlength (ls ++ [Byte.zero]) = Zlength ls + 1) by (autorewrite with sublist; auto).
  forward. normalize.
  forward. fold_Vbyte.
 forward_if.
  { forward. 
    Exists (offset_val i str).
    entailer!.
    left. exists i. split3; auto. rewrite app_Znth1; auto. cstring. }
  { forward_if.
    { forward.
      Exists nullval; rewrite !map_app; entailer!.
      right. split; auto.
      assert (i = Zlength ls) by cstring.
      subst i.
     autorewrite with sublist in H2; auto. }
  forward.
  Exists (i+1); entailer!.
  assert (i <> Zlength ls) by cstring.
  split. omega.
  rewrite (sublist_split 0 i) by rep_omega. rewrite Forall_app. split; auto.
  rewrite sublist_len_1 by rep_omega. repeat constructor.
  rewrite app_Znth1 in H4 by rep_omega. auto.
  }
-
  Intros i.
  forward.
  Exists i.
 entailer!.
Qed.

Lemma split_data_at_app_tschar:
 forall sh n (al bl: list val) p ,
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

Lemma body_strcat: semax_body Vprog Gprog f_strcat strcat_spec.
Proof.
start_function.
unfold cstringn, cstring in *.
rename sd into ld. rename ss into ls.
Intros.
forward.
forward_loop (EX i : Z,
    PROP (0 <= i < Zlength ld + 1)
    LOCAL (temp _i (Vint (Int.repr i)); temp _dest dest; temp _src src)
    SEP (data_at sh (tarray tschar n)
          (map Vbyte (ld ++ [Byte.zero]) ++
           list_repeat (Z.to_nat (n - (Zlength ld + 1))) Vundef) dest;
   data_at sh' (tarray tschar (Zlength ls + 1))
     (map Vbyte (ls ++ [Byte.zero])) src))
 continue: (EX i : Z,
    PROP (0 <= i < Zlength ld + 1)
    LOCAL (temp _i (Vint (Int.repr (i-1))); temp _dest dest; temp _src src)
    SEP (data_at sh (tarray tschar n)
          (map Vbyte (ld ++ [Byte.zero]) ++
           list_repeat (Z.to_nat (n - (Zlength ld + 1))) Vundef) dest;
   data_at sh' (tarray tschar (Zlength ls + 1))
     (map Vbyte (ls ++ [Byte.zero])) src))
  break: (PROP ( )
   LOCAL (temp _i (Vint (Int.repr (Zlength ld))); temp _dest dest; 
   temp _src src)
   SEP (data_at sh (tarray tschar n)
          (map Vbyte (ld ++ [Byte.zero]) ++
           list_repeat (Z.to_nat (n - (Zlength ld + 1))) Vundef) dest;
   data_at sh' (tarray tschar (Zlength ls + 1))
     (map Vbyte (ls ++ [Byte.zero])) src)).
-
  Exists 0; entailer!.
-
  Intros i.
  forward.
  { entailer!. }
  { entailer!. autorewrite with sublist. normalize.  }
  autorewrite with sublist; normalize.
  forward.
  forward_if.
  + forward.
    entailer!. f_equal. f_equal. cstring.
  +
    forward.
    Exists (i+1); entailer!. cstring.
- Intros i.
   forward.
   Exists i. entailer!. 
-
  abbreviate_semax.
  forward.
  forward_loop (EX j : Z,
    PROP (0 <= j < Zlength ls + 1)
    LOCAL (temp _j (Vint (Int.repr j)); temp _i (Vint (Int.repr (Zlength ld)));
           temp _dest dest; temp _src src)
    SEP (data_at sh (tarray tschar n)
          (map Vbyte (ld ++ sublist 0 j ls) ++
           list_repeat (Z.to_nat (n - (Zlength ld + j))) Vundef) dest;
         data_at sh' (tarray tschar (Zlength ls + 1))
           (map Vbyte (ls ++ [Byte.zero])) src))
   continue: (EX j : Z,
    PROP (0 <= j < Zlength ls + 1)
    LOCAL (temp _j (Vint (Int.repr (j-1))); temp _i (Vint (Int.repr (Zlength ld)));
           temp _dest dest; temp _src src)
    SEP (data_at sh (tarray tschar n)
          (map Vbyte (ld ++ sublist 0 j ls) ++
           list_repeat (Z.to_nat (n - (Zlength ld + j))) Vundef) dest;
         data_at sh' (tarray tschar (Zlength ls + 1))
           (map Vbyte (ls ++ [Byte.zero])) src)).
  { Exists 0; entailer!.  autorewrite with sublist.
    rewrite !map_app. rewrite <- app_assoc.
    rewrite split_data_at_app_tschar by list_solve.
    rewrite (split_data_at_app_tschar _ n) by list_solve.
    autorewrite with sublist.
    cancel.    
   }
  { Intros j.
  assert (Zlength (ls ++ [Byte.zero]) = Zlength ls + 1) by (autorewrite with sublist; auto).
  forward. normalize.
  forward. fold_Vbyte.
  forward.
  entailer!.
  clear H3.
  rewrite upd_Znth_app2 by list_solve.
  autorewrite with sublist.
  forward_if.
  + forward.
      autorewrite with sublist.
      rewrite prop_true_andp 
        by (intro Hx; apply in_app in Hx; destruct Hx; contradiction).
      cancel.
    assert (j = Zlength ls) by cstring; subst.
    autorewrite with sublist.
    apply derives_refl'.
    unfold data_at; f_equal. 
    replace (n - (Zlength ld + Zlength ls))
     with (1 + (n - (Zlength ld + Zlength ls+1))) by rep_omega.
    rewrite <- list_repeat_app' by rep_omega.
    rewrite upd_Znth_app1 by list_solve.
    rewrite app_assoc.
    simpl.
    rewrite !map_app.
    reflexivity.
 +
  forward.
  Exists (j+1).
  destruct (zlt j (Zlength ls)); [ | cstring].
  entailer!.
  change (field_at Tsh (tarray tschar n) []) with (data_at Tsh (tarray tschar n)).
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
  }
 + Intros j. forward. Exists j. entailer!.
Qed.

Lemma body_strcmp: semax_body Vprog Gprog f_strcmp strcmp_spec.
Proof.
start_function.
unfold cstring in *.
rename s1 into ls1. rename s2 into ls2.
forward.
Intros.
forward_loop (EX i : Z,
  PROP (0 <= i < Zlength ls1 + 1; 0 <= i < Zlength ls2 + 1;
        sublist 0 i ls1 = sublist 0 i ls2)
  LOCAL (temp _str1 str1; temp _str2 str2; temp _i (Vint (Int.repr i)))
  SEP (data_at sh1 (tarray tschar (Zlength ls1 + 1))
          (map Vbyte (ls1 ++ [Byte.zero])) str1;
       data_at sh2 (tarray tschar (Zlength ls2 + 1))
          (map Vbyte (ls2 ++ [Byte.zero])) str2))
  continue: (EX i : Z,
  PROP (0 <= i < Zlength ls1 + 1; 0 <= i < Zlength ls2 + 1;
        sublist 0 i ls1 = sublist 0 i ls2)
  LOCAL (temp _str1 str1; temp _str2 str2; temp _i (Vint (Int.repr (i-1))))
  SEP (data_at sh1 (tarray tschar (Zlength ls1 + 1))
          (map Vbyte (ls1 ++ [Byte.zero])) str1;
       data_at sh2 (tarray tschar (Zlength ls2 + 1))
          (map Vbyte (ls2 ++ [Byte.zero])) str2)).
- Exists 0; entailer!.
- Intros i.
  assert (Zlength (ls1 ++ [Byte.zero]) = Zlength ls1 + 1) by (autorewrite with sublist; auto).
  forward. normalize.
  assert (Zlength (ls2 ++ [Byte.zero]) = Zlength ls2 + 1) by (autorewrite with sublist; auto).
  forward. fold_Vbyte.
  assert (Znth i (ls1 ++ [Byte.zero]) = Byte.zero <-> i = Zlength ls1) as Hs1.
  { split; [|intro; subst; rewrite app_Znth2, Zminus_diag by omega; auto].
    destruct (zlt i (Zlength ls1)); [|omega].
    intro X; lapply (Znth_In i ls1); [|omega]. cstring. }
  assert (Znth i (ls2 ++ [Byte.zero]) = Byte.zero <-> i = Zlength ls2) as Hs2.
  { split; [|intro; subst; rewrite app_Znth2, Zminus_diag by omega; auto].
    destruct (zlt i (Zlength ls2)); [|omega].
    intro X; lapply (Znth_In i ls2); [|omega]. cstring. }
  forward. normalize.
  forward. fold_Vbyte.
  forward_if (temp _t'1 (Val.of_bool (Z.eqb i (Zlength ls1) && Z.eqb i (Zlength ls2)))).
  { forward.
    simpl force_val.
    rewrite Hs1 in *.
    destruct (Byte.eq_dec (Znth i (ls2 ++ [Byte.zero])) Byte.zero).
    + rewrite e; simpl force_val.
         assert (i = Zlength ls2) by cstring.
        rewrite  (proj2 Hs1 H6).
     rewrite (proj2 (Z.eqb_eq i (Zlength ls1)) H6).
     rewrite (proj2 (Z.eqb_eq i (Zlength ls2)) H7).
     entailer!.
  +
    rewrite Int.eq_false.
     rewrite (proj2 (Z.eqb_eq i (Zlength ls1)) H6).
     rewrite Hs2 in n.
     rewrite (proj2 (Z.eqb_neq i (Zlength ls2))) by auto.
    entailer!.
     contradict n.
     apply repr_inj_signed in n; try rep_omega. normalize in n.
 }
  { forward.
    entailer!.
    destruct (i =? Zlength ls1) eqn: Heq; auto.
    rewrite Z.eqb_eq in Heq; tauto. }
  forward_if.
 +
  rewrite andb_true_iff in H6; destruct H6.
  rewrite Z.eqb_eq in H6,H7.
  forward.
  Exists (Int.repr 0).
  entailer!. simpl.
  autorewrite with sublist in H3.
  auto.
 +
  deadvars!.
  rewrite andb_false_iff in H6. rewrite !Z.eqb_neq in H6.
  forward_if.
  *
    forward. Exists (Int.repr (-1)). entailer!.
    simpl. intro; subst. omega.
 *
   forward_if.
   forward.
   Exists (Int.repr 1). entailer!. simpl. intro. subst. omega.

   assert (H17: Byte.signed (Znth i (ls1 ++ [Byte.zero])) =
     Byte.signed (Znth i (ls2 ++ [Byte.zero]))) by omega.
   normalize in H17. clear H7 H8.
   forward.
   Exists (i+1).
   entailer!.
   clear H7 H8.
   clear H13 H14 H12 PNstr1 PNstr2.
   clear H10 H11 H9.
   destruct (zlt i (Zlength ls1)).
  2:{
         rewrite app_Znth2 in Hs1 by rep_omega.
         destruct (zeq i (Zlength ls1)); [ | omega].
         subst.
         destruct H6; [congruence | ].
         assert (Zlength ls1 < Zlength ls2) by omega.
         rewrite app_Znth2 in H17 by rep_omega.
         rewrite app_Znth1 in H17 by rep_omega.
         rewrite Z.sub_diag in H17. contradiction H0.
         change (Znth 0 [Byte.zero]) with Byte.zero in H17. rewrite H17.
         apply Znth_In. omega.
   }
  destruct (zlt i (Zlength ls2)).
  2:{
         rewrite app_Znth2 in Hs2 by rep_omega.
         destruct (zeq i (Zlength ls2)); [ | omega].
         subst.
         destruct H6; [ | congruence].
         assert (Zlength ls1 > Zlength ls2) by omega.
         rewrite app_Znth1 in H17 by rep_omega.
         rewrite app_Znth2 in H17 by rep_omega.
         rewrite Z.sub_diag in H17. contradiction H.
         change (Znth 0 [Byte.zero]) with Byte.zero in H17. rewrite <- H17.
         apply Znth_In. omega.
   }
  rewrite (sublist_split 0 i (i+1)) by omega.
  rewrite (sublist_split 0 i (i+1)) by omega.
  f_equal; auto.
  rewrite !sublist_len_1 by omega.
  rewrite !app_Znth1 in H17 by list_solve.
  split. rep_omega. split. rep_omega.
  f_equal; auto. f_equal. auto.
 -
  Intros i.
  forward.
  Exists i.
  entailer!.
Qed.

Lemma body_strcpy: semax_body Vprog Gprog f_strcpy strcpy_spec.
Proof.
start_function.
unfold cstring,cstringn in *.
rename s into ls.
forward.
Intros.
forward_loop (EX i : Z,
  PROP (0 <= i < Zlength ls + 1)
  LOCAL (temp _i (Vint (Int.repr i)); temp _dest dest; temp _src src)
  SEP (data_at sh (tarray tschar n)
        (map Vbyte (sublist 0 i ls) ++ list_repeat (Z.to_nat (n - i)) Vundef) dest;
       data_at sh' (tarray tschar (Zlength ls + 1)) (map Vbyte (ls ++ [Byte.zero])) src))
 continue: (EX i : Z,
  PROP (0 <= i < Zlength ls + 1)
  LOCAL (temp _i (Vint (Int.repr (i-1))); temp _dest dest; temp _src src)
  SEP (data_at sh (tarray tschar n)
        (map Vbyte (sublist 0 i ls) ++ list_repeat (Z.to_nat (n - i)) Vundef) dest;
       data_at sh' (tarray tschar (Zlength ls + 1)) (map Vbyte (ls ++ [Byte.zero])) src)).
*
 Exists 0. rewrite Z.sub_0_r; entailer!.
*
 Intros i.
 assert (Zlength (ls ++ [Byte.zero]) = Zlength ls + 1) by (autorewrite with sublist; auto).
 forward. normalize.
 forward. fold_Vbyte.
 forward.
 forward_if.
+ forward.
   entailer!.
  assert (i = Zlength ls) by cstring. subst i.
  change (field_at Tsh (tarray tschar n) []) with (data_at Tsh (tarray tschar n)).
  rewrite upd_Znth_app2 by list_solve.
  autorewrite with sublist.
  rewrite !map_app.
  rewrite <- app_assoc.
   rewrite (split_data_at_app_tschar _ n) by list_solve.
   rewrite (split_data_at_app_tschar _ n) by list_solve.
   autorewrite with sublist.
   replace (n - Zlength ls) with (1 + (n - (Zlength ls + 1))) at 2 by list_solve.
  rewrite <- list_repeat_app' by omega.
  rewrite upd_Znth_app1 by list_solve.
  rewrite !split_data_at_app_tschar by list_solve.
  cancel.
+
   assert (i < Zlength ls) by cstring.
  forward.
  Exists (i+1). entailer!. 
  autorewrite with sublist.
  rewrite (sublist_split 0 i (i+1)) by list_solve.
  rewrite !map_app. rewrite <- app_assoc.
  autorewrite with sublist.
  change (field_at Tsh (tarray tschar n) []) with (data_at Tsh (tarray tschar n)).
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
*
  Intros i.
  forward.
  Exists i.
  entailer!.
Qed.

Module Alternate.

(* Alternate proofs of these functions, using the form of "forward_loop"
  that relies on semax_loop_nocontinue *)

Lemma body_strlen: semax_body Vprog Gprog f_strlen strlen_spec.
Proof.
start_function.
unfold cstring in *.
rename s into ls.
Intros.
forward.
forward_loop  (EX i : Z,
  PROP (0 <= i < Zlength ls + 1)
  LOCAL (temp _str str; temp _i (Vptrofs (Ptrofs.repr i)))
  SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str)).
*
Exists 0. entailer!.
*
Intros i.
assert (Zlength (ls ++ [Byte.zero]) = Zlength ls + 1) by (autorewrite with sublist; auto).
forward.
normalize.
forward_if.
forward.
entailer!. f_equal. f_equal. cstring.
forward. (* entailer!.  *)
Exists (i+1).
entailer!. cstring.
Qed.

Lemma body_strchr: semax_body Vprog Gprog f_strchr strchr_spec.
Proof.
start_function.
forward.
unfold cstring in *.
rename s into ls.
Intros.
forward_loop (EX i : Z,
  PROP (0 <= i < Zlength ls + 1; Forall (fun d => d <> c) (sublist 0 i ls))
  LOCAL (temp _str str; temp _c (Vbyte c); temp _i (Vint (Int.repr i)))
  SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str)).
  Exists 0; rewrite sublist_nil; entailer!.
- Intros i. 
  assert (Zlength (ls ++ [Byte.zero]) = Zlength ls + 1) by (autorewrite with sublist; auto).
  forward. normalize.
  forward. fold_Vbyte.
  forward_if (Znth i (ls ++ [Byte.zero]) <> c).

  { forward. 
    Exists (offset_val i str).
    entailer!.
    left. exists i. split3; auto. rewrite app_Znth1; auto. cstring. }
  { forward.
    entailer!. }
  Intros.
  forward_if. 
  { forward.
    Exists nullval; rewrite !map_app; entailer!.
    right. split; auto.
    assert (i = Zlength ls) by cstring.
    subst i.
    autorewrite with sublist in H2; auto. }
  forward. (* entailer!. *)
  Exists (i+1); entailer!.
  assert (i <> Zlength ls) by cstring.
  split. omega.
  rewrite (sublist_split 0 i) by rep_omega. rewrite Forall_app. split; auto.
  rewrite sublist_len_1 by rep_omega. repeat constructor.
  rewrite app_Znth1 in H4 by rep_omega. auto.
Qed.

Lemma body_strcat: semax_body Vprog Gprog f_strcat strcat_spec.
Proof.
start_function.
unfold cstringn, cstring in *.
rename sd into ld. rename ss into ls.
Intros.
forward.
forward_loop (EX i : Z,
    PROP (0 <= i < Zlength ld + 1)
    LOCAL (temp _i (Vint (Int.repr i)); temp _dest dest; temp _src src)
    SEP (data_at sh (tarray tschar n)
          (map Vbyte (ld ++ [Byte.zero]) ++
           list_repeat (Z.to_nat (n - (Zlength ld + 1))) Vundef) dest;
   data_at sh' (tarray tschar (Zlength ls + 1))
     (map Vbyte (ls ++ [Byte.zero])) src))
  break: (PROP ( )
   LOCAL (temp _i (Vint (Int.repr (Zlength ld))); temp _dest dest; 
   temp _src src)
   SEP (data_at sh (tarray tschar n)
          (map Vbyte (ld ++ [Byte.zero]) ++
           list_repeat (Z.to_nat (n - (Zlength ld + 1))) Vundef) dest;
   data_at sh' (tarray tschar (Zlength ls + 1))
     (map Vbyte (ls ++ [Byte.zero])) src)).
-
  Exists 0; entailer!.
-
  Intros i.
  forward.
  { entailer!. }
  { entailer!. autorewrite with sublist. normalize.  }
  autorewrite with sublist; normalize.
  forward.
  forward_if (*  (Znth i (ld ++ [Byte.zero]) Byte.zero <> Byte.zero). *)
  + forward.
   (*  entailer!. f_equal. f_equal. cstring. *)
  +
    forward. entailer!. f_equal. f_equal. cstring. 
  +
    forward.
    Exists (i+1); entailer!. cstring.
-
  abbreviate_semax.
  forward.
  forward_loop (EX j : Z,
    PROP (0 <= j < Zlength ls + 1)
    LOCAL (temp _j (Vint (Int.repr j)); temp _i (Vint (Int.repr (Zlength ld)));
           temp _dest dest; temp _src src)
    SEP (data_at sh (tarray tschar n)
          (map Vbyte (ld ++ sublist 0 j ls) ++
           list_repeat (Z.to_nat (n - (Zlength ld + j))) Vundef) dest;
         data_at sh' (tarray tschar (Zlength ls + 1))
           (map Vbyte (ls ++ [Byte.zero])) src)).
  { Exists 0; entailer!.  autorewrite with sublist.
    rewrite !map_app. rewrite <- app_assoc.
    rewrite split_data_at_app_tschar by list_solve.
    rewrite (split_data_at_app_tschar _ n) by list_solve.
    autorewrite with sublist.
    cancel.    
   }
  { Intros j.
  assert (Zlength (ls ++ [Byte.zero]) = Zlength ls + 1) by (autorewrite with sublist; auto).
  forward. normalize.
  forward. fold_Vbyte.
  forward.
  entailer!.
  clear H3.
  rewrite upd_Znth_app2 by list_solve.
  autorewrite with sublist.
  forward_if.
  + forward.
      autorewrite with sublist.
      rewrite prop_true_andp 
        by (intro Hx; apply in_app in Hx; destruct Hx; contradiction).
      cancel.
    assert (j = Zlength ls) by cstring; subst.
    autorewrite with sublist.
    apply derives_refl'.
    unfold data_at; f_equal. 
    replace (n - (Zlength ld + Zlength ls))
     with (1 + (n - (Zlength ld + Zlength ls+1))) by rep_omega.
    rewrite <- list_repeat_app' by rep_omega.
    rewrite upd_Znth_app1 by list_solve.
    rewrite app_assoc.
    simpl.
    rewrite !map_app.
    reflexivity.
 +
  forward. (* entailer!. *)
  Exists (j+1).
  destruct (zlt j (Zlength ls)); [ | cstring].
  entailer!.
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
 }
Qed.

Lemma body_strcmp: semax_body Vprog Gprog f_strcmp strcmp_spec.
Proof.
start_function.
unfold cstring in *.
rename s1 into ls1. rename s2 into ls2.
forward.
Intros.
forward_loop (EX i : Z,
  PROP (0 <= i < Zlength ls1 + 1; 0 <= i < Zlength ls2 + 1;
        sublist 0 i ls1 = sublist 0 i ls2)
  LOCAL (temp _str1 str1; temp _str2 str2; temp _i (Vint (Int.repr i)))
  SEP (data_at sh1 (tarray tschar (Zlength ls1 + 1))
          (map Vbyte (ls1 ++ [Byte.zero])) str1;
       data_at sh2 (tarray tschar (Zlength ls2 + 1))
          (map Vbyte (ls2 ++ [Byte.zero])) str2)).
- Exists 0; entailer!.
- Intros i.
  assert (Zlength (ls1 ++ [Byte.zero]) = Zlength ls1 + 1) by (autorewrite with sublist; auto).
  forward. normalize.
  assert (Zlength (ls2 ++ [Byte.zero]) = Zlength ls2 + 1) by (autorewrite with sublist; auto).
  forward. fold_Vbyte.
  assert (Znth i (ls1 ++ [Byte.zero]) = Byte.zero <-> i = Zlength ls1) as Hs1.
  { split; [|intro; subst; rewrite app_Znth2, Zminus_diag by omega; auto].
    destruct (zlt i (Zlength ls1)); [|omega].
    intro X; lapply (Znth_In i ls1); [|omega]. cstring. }
  assert (Znth i (ls2 ++ [Byte.zero]) = Byte.zero <-> i = Zlength ls2) as Hs2.
  { split; [|intro; subst; rewrite app_Znth2, Zminus_diag by omega; auto].
    destruct (zlt i (Zlength ls2)); [|omega].
    intro X; lapply (Znth_In i ls2); [|omega]. cstring. }
  forward. normalize.
  forward. fold_Vbyte.
  forward_if (temp _t'1 (Val.of_bool (Z.eqb i (Zlength ls1) && Z.eqb i (Zlength ls2)))).
  { forward.
    simpl force_val. normalize.
    rewrite Hs1 in *.
    destruct (Byte.eq_dec (Znth i (ls2 ++ [Byte.zero])) Byte.zero).
    + rewrite e; simpl force_val.
         assert (i = Zlength ls2) by cstring.
        rewrite  (proj2 Hs1 H6).
     rewrite (proj2 (Z.eqb_eq i (Zlength ls1)) H6).
     rewrite (proj2 (Z.eqb_eq i (Zlength ls2)) H7).
     entailer!.
  +
    rewrite Int.eq_false.
     rewrite (proj2 (Z.eqb_eq i (Zlength ls1)) H6).
     rewrite Hs2 in n.
     rewrite (proj2 (Z.eqb_neq i (Zlength ls2))) by auto.
    entailer!.
     contradict n.
     apply repr_inj_signed in n; try rep_omega. normalize in n.
 }
  { forward.
    entailer!.
    destruct (i =? Zlength ls1) eqn: Heq; auto.
    rewrite Z.eqb_eq in Heq; tauto. }
  forward_if. 
 +
  rewrite andb_true_iff in H6; destruct H6.
  rewrite Z.eqb_eq in H6,H7.
  forward.
  Exists (Int.repr 0).
  entailer!. simpl.
  autorewrite with sublist in H3.
  auto.
 +
  rewrite andb_false_iff in H6. rewrite !Z.eqb_neq in H6.
  forward_if.
  *
    forward. Exists (Int.repr (-1)). entailer!.
    simpl. intro; subst. omega.
 *
   forward_if.
   forward.
   Exists (Int.repr 1). entailer!. simpl. intro. subst. omega.

   assert (H17: Byte.signed (Znth i (ls1 ++ [Byte.zero])) =
     Byte.signed (Znth i (ls2 ++ [Byte.zero]))) by omega.
   normalize in H17. clear H7 H8.
   forward.
   Exists (i+1).
   entailer!.
   clear - H17 H6 Hs1 Hs2 H3 H1 H2 H H0.
   destruct (zlt i (Zlength ls1)).
  2:{
         assert (i = Zlength ls1) by omega. subst.
         destruct H6; [congruence | ].
         assert (Zlength ls1 < Zlength ls2) by omega.
         rewrite app_Znth2 in H17 by rep_omega.
         rewrite app_Znth1 in H17 by rep_omega.
         rewrite Z.sub_diag in H17. contradiction H0.
         change (Znth 0 [Byte.zero]) with Byte.zero in H17.
         rewrite H17. apply Znth_In. omega.
   }
  destruct (zlt i (Zlength ls2)).
  2:{
         assert (i = Zlength ls2) by omega. subst.
         destruct H6; [ | congruence].
         assert (Zlength ls1 > Zlength ls2) by omega.
         rewrite app_Znth1 in H17 by rep_omega.
         rewrite app_Znth2 in H17 by rep_omega.
         rewrite Z.sub_diag in H17. contradiction H.
         change (Znth 0 [Byte.zero]) with Byte.zero in H17.
         rewrite <- H17.  apply Znth_In. omega.
   }
  rewrite (sublist_split 0 i (i+1)) by omega.
  rewrite (sublist_split 0 i (i+1)) by omega.
  f_equal; auto.
  rewrite !sublist_len_1 by omega.
  autorewrite with sublist in H17.
  split. rep_omega. split. rep_omega.
  f_equal; auto. f_equal. auto.
Qed.

Lemma body_strcpy: semax_body Vprog Gprog f_strcpy strcpy_spec.
Proof.
start_function.
unfold cstring,cstringn in *.
rename s into ls.
forward.
Intros.
forward_loop (EX i : Z,
  PROP (0 <= i < Zlength ls + 1)
  LOCAL (temp _i (Vint (Int.repr i)); temp _dest dest; temp _src src)
  SEP (data_at sh (tarray tschar n)
        (map Vbyte (sublist 0 i ls) ++ list_repeat (Z.to_nat (n - i)) Vundef) dest;
       data_at sh' (tarray tschar (Zlength ls + 1)) (map Vbyte (ls ++ [Byte.zero])) src)).
*
 Exists 0. rewrite Z.sub_0_r; entailer!.
*
 Intros i.
 assert (Zlength (ls ++ [Byte.zero]) = Zlength ls + 1) by (autorewrite with sublist; auto).
 forward. normalize.
 forward. fold_Vbyte.
 forward.
 forward_if.
+ forward.
   entailer!.
  assert (i = Zlength ls) by cstring. subst i.
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
+
   assert (i < Zlength ls) by cstring.
  forward.
  Exists (i+1). entailer!.
  rewrite upd_Znth_app2 by list_solve.
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

End Alternate.


