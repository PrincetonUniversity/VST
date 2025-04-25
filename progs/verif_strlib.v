Require Import VST.floyd.proofauto.
Require Import VST.floyd.compat. Import NoOracle.
Require Import VST.progs.strlib.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition strchr_spec :=
 DECLARE _strchr
  WITH sh: share, str : val, s : list byte, c : byte
  PRE  [ tptr tschar, tint ]
    PROP (readable_share sh; c <> Byte.zero)
    PARAMS (str; Vbyte c)
    SEP (cstring sh s str)
  POST [ tptr tschar ]
   EX r : val,
    PROP ((exists i, Znth i s = c /\ Forall (fun d => d<>c) (sublist 0 i s)
                     /\ r = offset_val i str)
       \/ (Forall (fun d => d<>c) s /\ r = nullval))
    RETURN (r)
    SEP (cstring sh s str).

Definition strcat_spec :=
 DECLARE _strcat
  WITH sh: share, sh': share, dest : val, sd : list byte, n : Z, src : val, ss : list byte
  PRE  [ tptr tschar, tptr tschar ]
    PROP (writable_share sh; readable_share sh'; Zlength sd + Zlength ss < n)
    PARAMS (dest; src)
    SEP (cstringn sh sd n dest; cstring sh' ss src)
  POST [ tptr tschar ]
    PROP ()
    RETURN (dest)
    SEP (cstringn sh (sd ++ ss) n dest; cstring sh' ss src).

Definition strcmp_spec :=
 DECLARE _strcmp
  WITH sh1: share, sh2: share, str1 : val, s1 : list byte, str2 : val, s2 : list byte
  PRE [ tptr tschar, tptr tschar ]
    PROP (readable_share sh1; readable_share sh2)
    PARAMS (str1; str2)
    SEP (cstring sh1 s1 str1; cstring sh2 s2 str2)
  POST [ tint ]
   EX i : int,
    PROP (if Int.eq_dec i Int.zero then s1 = s2 else s1 <> s2)
    RETURN (Vint i)
    SEP (cstring sh1 s1 str1; cstring sh2 s2 str2).

Definition strcpy_spec :=
 DECLARE _strcpy
  WITH sh: share, sh': share, dest : val, n : Z, src : val, s : list byte
  PRE [ tptr tschar, tptr tschar ]
    PROP (writable_share sh; readable_share sh'; Zlength s < n)
    PARAMS (dest; src)
    SEP (data_at_ sh (tarray tschar n) dest; cstring sh' s src)
  POST [ tptr tschar ]
    PROP ()
    RETURN (dest)
    SEP (cstringn sh s n dest; cstring sh' s src).

Definition strlen_spec :=
 DECLARE _strlen
  WITH sh: share, s : list byte, str: val
  PRE [ tptr tschar ]
    PROP (readable_share sh)
    PARAMS (str)
    SEP (cstring sh s str)
  POST [ size_t ]
    PROP ()
    RETURN (Vptrofs (Ptrofs.repr (Zlength s)))
    SEP (cstring sh s str).

Definition Gprog : funspecs :=
         ltac:(with_library prog [ strchr_spec; strcat_spec; strcmp_spec ]).

#[export] Hint Rewrite Z.add_simpl_r Z.sub_simpl_r : norm entailer_rewrite.

Lemma body_strlen: semax_body Vprog Gprog f_strlen strlen_spec.
Proof.
start_function.
unfold cstring in *.
rename s into ls.
forward.
forward_loop (EX i : Z,
  PROP (0 <= i < Zlength ls + 1)
  LOCAL (temp _str str; temp _i (Vptrofs (Ptrofs.repr i)))
  SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str)).
*
Exists 0. entailer!!.
*
Intros i.
forward.
forward_if.
forward.
entailer!!. repeat f_equal. cstring.
forward. 
Exists (i+1).
entailer!!. cstring.
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
  LOCAL (temp _str str; temp _c (Vbyte c); temp _i (Vptrofs (Ptrofs.repr i)))
  SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str)).
  Exists 0; rewrite sublist_nil; entailer!!.
- Intros i. 
  assert (Zlength (ls ++ [Byte.zero]) = Zlength ls + 1) by (autorewrite with sublist; auto).
  forward.
  forward. fold_Vbyte.
 forward_if.
  { forward. simpl. 
    Exists (offset_val i str).
    entailer!!.
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
  split. lia.
  rewrite (sublist_split 0 i) by rep_lia. rewrite Forall_app. split; auto.
  rewrite sublist_len_1 by rep_lia. repeat constructor.
  rewrite app_Znth1 in H4 by rep_lia. auto.
  }
Qed.

Lemma split_data_at_app_tschar:
 forall sh n (al bl: list val) p,
   n = Zlength (al++bl) ->
   data_at sh (tarray tschar n) (al++bl) p =
         (data_at sh (tarray tschar (Zlength al)) al p
          * data_at sh (tarray tschar (n - Zlength al)) bl
                 (field_address0 (tarray tschar n) [ArraySubsc (Zlength al)] p)).
Proof.
intros.
apply (split2_data_at_Tarray_app _ n  sh tschar al bl); auto.
rewrite Zlength_app in H.
change (Zlength bl = n - Zlength al); lia.
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
    LOCAL (temp _i (Vptrofs (Ptrofs.repr i)); temp _dest dest; temp _src src)
    SEP (data_at sh (tarray tschar n)
          (map Vbyte (ld ++ [Byte.zero]) ++
           repeat Vundef (Z.to_nat (n - (Zlength ld + 1)))) dest;
   data_at sh' (tarray tschar (Zlength ls + 1))
     (map Vbyte (ls ++ [Byte.zero])) src))
  break: (PROP ( )
   LOCAL (temp _i (Vptrofs (Ptrofs.repr (Zlength ld))); temp _dest dest; 
   temp _src src)
   SEP (data_at sh (tarray tschar n)
          (map Vbyte (ld ++ [Byte.zero]) ++
           repeat Vundef (Z.to_nat (n - (Zlength ld + 1)))) dest;
   data_at sh' (tarray tschar (Zlength ls + 1))
     (map Vbyte (ls ++ [Byte.zero])) src)).
-
  Exists 0; entailer!!.
-
  Intros i.
  forward.
  { entailer!. }
  { entailer!. autorewrite with sublist norm. auto.  }
  autorewrite with sublist norm.
  forward.
  forward_if.
  + forward.
    entailer!!. f_equal. f_equal. cstring.
  +
    forward.
    Exists (i+1); entailer!. cstring.
-
  abbreviate_semax.
  forward.
  forward_loop (EX j : Z,
    PROP (0 <= j < Zlength ls + 1)
    LOCAL (temp _j (Vptrofs (Ptrofs.repr j)); temp _i (Vptrofs (Ptrofs.repr (Zlength ld)));
           temp _dest dest; temp _src src)
    SEP (data_at sh (tarray tschar n)
          (map Vbyte (ld ++ sublist 0 j ls) ++
           repeat Vundef (Z.to_nat (n - (Zlength ld + j)))) dest;
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
  forward.  autorewrite with norm.
  forward. fold_Vbyte.
  forward.
  entailer!!.
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
    f_equiv.
    replace (n - (Zlength ld + Zlength ls))
     with (1 + (n - (Zlength ld + Zlength ls+1))) by rep_lia.
    rewrite <- repeat_app' by rep_lia.
    rewrite upd_Znth_app1 by list_solve.
    rewrite app_assoc.
    simpl.
    rewrite !map_app.
    reflexivity.
 +
  forward.
  Exists (j+1).
  destruct (zlt j (Zlength ls)); [ | cstring].
  entailer!!.
  change (field_at Tsh (tarray tschar n) []) with (data_at Tsh (tarray tschar n)).
  rewrite (sublist_split 0 j (j+1)) by rep_lia.
  rewrite (app_assoc ld). rewrite !map_app.
  rewrite <- (app_assoc (_ ++ _)).
  rewrite (split_data_at_app_tschar _ n) by list_solve.
  rewrite (split_data_at_app_tschar _ n) by list_solve.
  replace (n - (Zlength ld + j))
    with (1 + (n - (Zlength ld + (j + 1)))) by rep_lia.
  rewrite <- repeat_app' by rep_lia.
  cancel.
  rewrite upd_Znth_app1 by (autorewrite with sublist; rep_lia).
  rewrite app_Znth1 by list_solve.
  rewrite sublist_len_1 by rep_lia.
  cancel.
  }
Qed.

Lemma byte_unsigned_signed_conversion: 
  forall i, Int.zero_ext 8 (Int.repr (Byte.signed i)) = Int.zero_ext 8 (Int.repr (Byte.unsigned i)).
Proof.
intros.
unfold Int.zero_ext.
f_equal.
rewrite !Zbits.Zzero_ext_mod by computable.
rewrite !Int.unsigned_repr_eq.
change (Int.modulus) with ((Int.modulus / 256) * 256)%Z.
rewrite !Zaux.Zmod_mod_mult by (compute; auto; congruence).
unfold Byte.signed.
if_tac; auto.
rewrite Zminus_mod.
change (Byte.modulus mod _) with 0.
rewrite Z.sub_0_r.
rewrite Zmod_mod.
auto.
Qed.

Lemma zero_ext_byte_repr_unsigned: forall i,
 Int.zero_ext 8 (Int.repr (Byte.unsigned i))= Int.repr (Byte.unsigned i).
Proof.
intros.
unfold Int.zero_ext.
rewrite !Zbits.Zzero_ext_mod by computable.
rewrite !Int.unsigned_repr_eq.
f_equal.
change (Int.modulus) with ((Int.modulus / 256) * 256)%Z.
rewrite !Zaux.Zmod_mod_mult by (compute; auto; congruence).
rewrite !Z.mod_small by apply Byte.unsigned_range; auto.
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
  LOCAL (temp _str1 str1; temp _str2 str2; temp _i (Vptrofs (Ptrofs.repr i)))
  SEP (data_at sh1 (tarray tschar (Zlength ls1 + 1))
          (map Vbyte (ls1 ++ [Byte.zero])) str1;
       data_at sh2 (tarray tschar (Zlength ls2 + 1))
          (map Vbyte (ls2 ++ [Byte.zero])) str2)).
- Exists 0; entailer!!.
- Intros i.
  assert (Zlength (ls1 ++ [Byte.zero]) = Zlength ls1 + 1) by (autorewrite with sublist; auto).
  forward. autorewrite with norm.
  assert (Zlength (ls2 ++ [Byte.zero]) = Zlength ls2 + 1) by (autorewrite with sublist; auto).
  forward.
  assert (Znth i (ls1 ++ [Byte.zero]) = Byte.zero <-> i = Zlength ls1) as Hs1.
  { split; [|intro; subst; rewrite app_Znth2, Zminus_diag by lia; auto].
    destruct (zlt i (Zlength ls1)); [|lia].
    intro X; lapply (Znth_In i ls1); [|lia]. cstring. }
  assert (Znth i (ls2 ++ [Byte.zero]) = Byte.zero <-> i = Zlength ls2) as Hs2.
  { split; [|intro; subst; rewrite app_Znth2, Zminus_diag by lia; auto].
    destruct (zlt i (Zlength ls2)); [|lia].
    intro X; lapply (Znth_In i ls2); [|lia]. cstring. }
  forward.
  forward.
  rewrite !Int.zero_ext_idem by computable.
  rewrite !byte_unsigned_signed_conversion.
  rewrite !zero_ext_byte_repr_unsigned.
  clear H4 H5.
  forward_if (temp _t'1 (bool2val (Z.eqb i (Zlength ls1) && Z.eqb i (Zlength ls2)))).
  { forward.
    entailer!!. f_equal.
    apply (f_equal Byte.repr) in H4. rewrite Byte.repr_unsigned in H4.
    apply Hs1 in H4. 
    rewrite (proj2 (Z.eqb_eq _ _) H4). simpl.
    destruct (zeq _ _); simpl.
    apply (f_equal Byte.repr) in e. rewrite Byte.repr_unsigned in e.
    apply Hs2 in e.
    rewrite (proj2 (Z.eqb_eq _ _) e). auto.
    apply Z.eqb_neq. contradict n.
    apply Hs2 in n. rewrite n. reflexivity.
 }
  { forward.
    entailer!!.
    destruct (i =? Zlength ls1) eqn: Heq; auto.
    destruct (i =? Zlength ls2) eqn: Heq2; auto.
    rewrite Z.eqb_eq in Heq, Heq2.
    subst.
    contradiction H4. list_simplify.
  }
  forward_if.
 +
  rewrite andb_true_iff in H4; destruct H4.
  rewrite Z.eqb_eq in H4,H5.
  forward.
  Exists (Int.repr 0).
  entailer!!. simpl.
  autorewrite with sublist in H3.
  auto.
 +
  rewrite andb_false_iff in H4. rewrite !Z.eqb_neq in H4.
  forward_if.
  *
    forward. Exists (Int.repr (-1)). entailer!!.
    simpl. intro; subst. lia.
 *
   forward_if.
   forward.
   Exists (Int.repr 1). entailer!.
   match type of H5 with ?a >= ?b => assert (H17: a=b) by lia end.
   clear H5 H6.
    apply (f_equal Byte.repr) in H17. rewrite !Byte.repr_unsigned in H17.
   forward.
   Exists (i+1).
   entailer!!.
   destruct (zlt i (Zlength ls1)).
  2:{
         rewrite app_Znth2 in Hs1 by rep_lia.
         destruct (zeq i (Zlength ls1)); [ | lia].
         subst.
         destruct H4; [congruence | ].
         assert (Zlength ls1 < Zlength ls2) by lia.
         rewrite app_Znth2 in H17 by rep_lia.
         rewrite app_Znth1 in H17 by rep_lia.
         rewrite Z.sub_diag in H17. contradiction H0.
         change (Znth 0 [Byte.zero]) with Byte.zero in H17. rewrite H17.
         apply Znth_In. lia.
   }
  destruct (zlt i (Zlength ls2)).
  2:{
         rewrite app_Znth2 in Hs2 by rep_lia.
         destruct (zeq i (Zlength ls2)); [ | lia].
         subst.
         destruct H4; [ | congruence].
         assert (Zlength ls1 > Zlength ls2) by lia.
         rewrite app_Znth1 in H17 by rep_lia.
         rewrite app_Znth2 in H17 by rep_lia.
         rewrite Z.sub_diag in H17. contradiction H.
         change (Znth 0 [Byte.zero]) with Byte.zero in H17. rewrite <- H17.
         apply Znth_In. lia.
   }
  rewrite (sublist_split 0 i (i+1)) by lia.
  rewrite (sublist_split 0 i (i+1)) by lia.
  f_equal; auto.
  rewrite !sublist_len_1 by lia.
  rewrite !app_Znth1 in H17 by list_solve.
  split. rep_lia. split. rep_lia.
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
  LOCAL (temp _i (Vptrofs (Ptrofs.repr i)); temp _dest dest; temp _src src)
  SEP (data_at sh (tarray tschar n)
        (map Vbyte (sublist 0 i ls) ++ repeat Vundef (Z.to_nat (n - i))) dest;
       data_at sh' (tarray tschar (Zlength ls + 1)) (map Vbyte (ls ++ [Byte.zero])) src)).
*
 Exists 0. rewrite Z.sub_0_r; entailer!; simpl; entailer!.
*
 Intros i.
 assert (Zlength (ls ++ [Byte.zero]) = Zlength ls + 1) by (autorewrite with sublist; auto).
 forward. autorewrite with norm.
 forward. fold_Vbyte.
 forward.
 forward_if.
+ forward.
   entailer!!.
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
  rewrite <- repeat_app' by lia.
  rewrite upd_Znth_app1 by list_solve.
  rewrite !split_data_at_app_tschar by list_solve.
  cancel.
+
   assert (i < Zlength ls) by cstring.
  forward.
  Exists (i+1). entailer!!. 
  autorewrite with sublist.
  rewrite (sublist_split 0 i (i+1)) by list_solve.
  rewrite !map_app. rewrite <- app_assoc.
  autorewrite with sublist.
  change (field_at Tsh (tarray tschar n) []) with (data_at Tsh (tarray tschar n)).
  rewrite !(split_data_at_app_tschar _ n) by list_solve.
  autorewrite with sublist.
   replace (n - i) with (1 + (n-(i+ 1))) at 2 by list_solve.
  rewrite <- repeat_app' by lia.
  autorewrite with sublist.
  cancel.
  rewrite !split_data_at_app_tschar by list_solve.
  autorewrite with sublist.
  rewrite sublist_len_1 by lia.
  simpl. cancel.
Qed.

Module Alternate.

(* Alternate proofs of these functions, using list solver *)

Lemma body_strlen: semax_body Vprog Gprog f_strlen strlen_spec.
Proof.
start_function.
unfold cstring in *.
rename s into ls.
forward.
forward_loop  (EX i : Z,
  PROP (0 <= i < Zlength ls + 1)
  LOCAL (temp _str str; temp _i (Vptrofs (Ptrofs.repr i)))
  SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str)).
all: finish.
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
  LOCAL (temp _str str; temp _c (Vbyte c); temp _i (Vptrofs (Ptrofs.repr i)))
  SEP (data_at sh (tarray tschar (Zlength ls + 1))
          (map Vbyte (ls ++ [Byte.zero])) str)).
all: finish.
Qed.

Lemma body_strcat: semax_body Vprog Gprog f_strcat strcat_spec.
Proof.
start_function.
unfold cstringn, cstring in *.
rename sd into ld. rename ss into ls.
forward.
forward_loop (EX i : Z,
    PROP (0 <= i < Zlength ld + 1)
    LOCAL (temp _i (Vptrofs (Ptrofs.repr i)); temp _dest dest; temp _src src)
    SEP (data_at sh (tarray tschar n)
          (map Vbyte (ld ++ [Byte.zero]) ++
           repeat Vundef (Z.to_nat (n - (Zlength ld + 1)))) dest;
   data_at sh' (tarray tschar (Zlength ls + 1))
     (map Vbyte (ls ++ [Byte.zero])) src))
  break: (PROP ( )
   LOCAL (temp _i (Vptrofs (Ptrofs.repr (Zlength ld))); temp _dest dest; 
   temp _src src)
   SEP (data_at sh (tarray tschar n)
          (map Vbyte (ld ++ [Byte.zero]) ++
           repeat Vundef (Z.to_nat (n - (Zlength ld + 1)))) dest;
   data_at sh' (tarray tschar (Zlength ls + 1))
     (map Vbyte (ls ++ [Byte.zero])) src)).
- (* before loop1 *)
  finish.
- (* loop1 body *)
  finish!.
-
  fastforward.
  forward_loop (EX j : Z,
    PROP (0 <= j < Zlength ls + 1)
    LOCAL (temp _j (Vptrofs (Ptrofs.repr j)); temp _i (Vptrofs (Ptrofs.repr (Zlength ld)));
           temp _dest dest; temp _src src)
    SEP (data_at sh (tarray tschar n)
          (map Vbyte (ld ++ sublist 0 j ls) ++
           repeat Vundef (Z.to_nat (n - (Zlength ld + j)))) dest;
         data_at sh' (tarray tschar (Zlength ls + 1))
           (map Vbyte (ls ++ [Byte.zero])) src)).
  all: finish.
Qed.

Lemma body_strcmp: semax_body Vprog Gprog f_strcmp strcmp_spec.
Proof.
start_function.
unfold cstring in *.
rename s1 into ls1. rename s2 into ls2.
fastforward.
forward_loop (EX i : Z,
  PROP (0 <= i < Zlength ls1 + 1; 0 <= i < Zlength ls2 + 1;
        forall (j:Z), 0 <= j < i -> Znth j ls1 = Znth j ls2)
  LOCAL (temp _str1 str1; temp _str2 str2; temp _i (Vptrofs (Ptrofs.repr i)))
  SEP (data_at sh1 (tarray tschar (Zlength ls1 + 1))
          (map Vbyte (ls1 ++ [Byte.zero])) str1;
       data_at sh2 (tarray tschar (Zlength ls2 + 1))
          (map Vbyte (ls2 ++ [Byte.zero])) str2)).
- finish.
- fastforward.
  forward_if (temp _t'1 (bool2val (Z.eqb i (Zlength ls1) && Z.eqb i (Zlength ls2)))).
  (* these two parts are not much simplified *)
  { forward.
    entailer!!. f_equal.
    rewrite !Int.zero_ext_idem in * by computable.
    rewrite byte_unsigned_signed_conversion,
         zero_ext_byte_repr_unsigned in H4 |-*.
    apply repr_inj_unsigned in H4; [ | rep_lia ..].
    apply (f_equal Byte.repr) in H4. rewrite Byte.repr_unsigned in H4.
    change (Byte.repr 0) with Byte.zero in H4.
    assert (i = Zlength ls1) by cstring.  clear H4 H1.
    rewrite (proj2 (Z.eqb_eq _ _) H5); simpl.
    rewrite eq_repr_zeq by rep_lia.
    destruct (zeq _ _); simpl. apply Z.eqb_eq.
    apply (f_equal Byte.repr) in e. rewrite Byte.repr_unsigned in e.
    change (Byte.repr 0) with Byte.zero in e.
    cstring.
    apply Z.eqb_neq. contradict n. subst.  rewrite n. list_simplify.
 }
  { forward.
    entailer!!.
    destruct (i =? Zlength ls1) eqn: Heq; auto.
    destruct (i =? Zlength ls2) eqn: Heq2; auto.
    rewrite Z.eqb_eq in Heq, Heq2.
    subst.
    contradiction H4. list_simplify.
  }
  rewrite !Int.zero_ext_idem by computable.
  rewrite !byte_unsigned_signed_conversion.
  rewrite !zero_ext_byte_repr_unsigned.
  forward_if.
 +
  rewrite andb_true_iff in H4; destruct H4.
  rewrite Z.eqb_eq in H4,H5. subst i.
  forward.
  Exists (Int.repr 0).
  entailer!!. simpl.
  apply Znth_eq_ext; auto.
 +
  rewrite andb_false_iff in H4. rewrite !Z.eqb_neq in H4.
  forward_if.
  *
    forward. Exists (Int.repr (-1)). entailer!!.
    simpl. intro; subst. lia.
 *
   forward_if.
   forward.
   Exists (Int.repr 1). entailer!.
   match type of H5 with ?a >= ?b => assert (H17: a=b) by lia end.
   clear H5 H6.
   apply (f_equal Byte.repr) in H17. rewrite !Byte.repr_unsigned in H17.
   forward.
   Exists (i+1).
   entailer!!.
   destruct H4.
   assert (Znth i (ls1 ++ [Byte.zero]) <> Byte.zero) by (intro; cstring).
   rewrite H17 in H5. assert (i <> Zlength ls2) by (intro; cstring).
   split3; try lia. intros. destruct (zeq j i). 2: apply H3; lia. subst.
   rewrite !app_Znth1 in H17 by lia. auto.
   assert (Znth i (ls2 ++ [Byte.zero]) <> Byte.zero) by (intro; cstring).
   rewrite <- H17 in H5. assert (i <> Zlength ls1) by (intro; cstring).
   split3; try lia. intros. destruct (zeq j i). 2: apply H3; lia. subst.
   rewrite !app_Znth1 in H17 by lia. auto.
Qed.

Lemma body_strcpy: semax_body Vprog Gprog f_strcpy strcpy_spec.
Proof.
start_function.
unfold cstring,cstringn in *.
rename s into ls.
fastforward.
forward_loop (EX i : Z,
  PROP (0 <= i < Zlength ls + 1)
  LOCAL (temp _i (Vptrofs (Ptrofs.repr i)); temp _dest dest; temp _src src)
  SEP (data_at sh (tarray tschar n)
        (map Vbyte (sublist 0 i ls) ++ repeat Vundef (Z.to_nat (n - i))) dest;
       data_at sh' (tarray tschar (Zlength ls + 1)) (map Vbyte (ls ++ [Byte.zero])) src)).
all: finish.
Qed.

End Alternate.
