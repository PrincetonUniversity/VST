Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import JMeq.
Local Open Scope nat.
Local Open Scope logic.

Lemma Zlength_list_repeat:
  forall {A} n (x:A), Zlength (list_repeat (Z.to_nat n) x) = Z.max 0 n.
Proof.
intros.
rewrite Zlength_correct, length_list_repeat.
destruct (zlt n 0).
rewrite Z.max_l by omega.
rewrite Z2Nat_neg by auto. reflexivity.
rewrite Z2Nat.id by omega.
rewrite Z.max_r by omega.
auto.
Qed.

Definition splice_into_list (lo hi n : Z) (source target : list val) : list val :=
   sublist 0 lo (target ++ list_repeat (Z.to_nat (lo - Zlength target)) Vundef)
   ++ sublist 0 (hi-lo) (source ++ list_repeat (Z.to_nat (hi-lo)) Vundef)
   ++ sublist hi n (target ++ list_repeat (Z.to_nat (n- Zlength target)) Vundef).

Lemma splice_into_list_simplify0:
  forall n src dst, 
    Zlength src = n ->
    Zlength dst = n ->
    splice_into_list 0 n n src dst = src.
Proof.
 intros.
 unfold splice_into_list.
rewrite !sublist_nil.
rewrite <- app_nil_end, app_nil_l.
pose proof (Zlength_nonneg src).
rewrite sublist_app by (rewrite ?Zlength_list_repeat, ?Z.max_r; omega).
rewrite ?Z.min_l by omega.
rewrite ?Z.max_r by omega.
rewrite sublist_nil, <- app_nil_end by omega.
apply sublist_same; omega.
Qed.

Lemma splice_into_list_simplify1:
  forall lo hi src tgt,
    lo = Zlength tgt ->
    (hi-lo = Zlength src)%Z ->
    splice_into_list lo hi hi src tgt = tgt++src.
Proof.
intros; subst; unfold splice_into_list.
pose proof (Zlength_nonneg tgt).
pose proof (Zlength_nonneg src).
rewrite H0.
rewrite Z.sub_diag.
change (Z.to_nat 0) with 0%nat; simpl.
rewrite <- app_nil_end.
rewrite sublist_same by omega.
f_equal.
rewrite (sublist_nil hi), <- app_nil_end.
rewrite sublist_app by (rewrite ?Zlength_list_repeat, ?Z.max_r; omega).
rewrite ?Z.min_l by omega.
rewrite ?Z.max_r by omega.
rewrite sublist_nil, <- app_nil_end.
apply sublist_same; omega.
Qed.

Lemma splice_into_list_simplify2:
  forall lo hi src tgt,
    lo = Zlength tgt ->
    (lo <= hi)%Z ->
    (hi-lo <= Zlength src)%Z ->
    splice_into_list lo hi hi src tgt = tgt++ sublist 0 (hi-lo) src.
Proof.
intros; subst; unfold splice_into_list.
pose proof (Zlength_nonneg tgt).
pose proof (Zlength_nonneg src).
repeat rewrite Z.sub_diag.
change (Z.to_nat 0) with 0.
unfold list_repeat at 1.
rewrite <- app_nil_end.
rewrite sublist_same by omega.
f_equal.
rewrite sublist_nil, <- app_nil_end by omega.
rewrite sublist_app by (rewrite ?Zlength_list_repeat, ?Z.max_r; omega).
rewrite ?Z.min_l by omega.
rewrite ?Z.max_r by omega.
rewrite sublist_nil, <- app_nil_end by omega.
auto.
Qed.

Lemma JMeq_skipn:
  forall ta tb n (la: list ta) (lb: list tb),
     ta=tb ->
     JMeq la lb ->
     JMeq (skipn n la) (skipn n lb).
Proof.
intros. subst tb. apply JMeq_eq in H0. subst lb. auto.
Qed.

Lemma JMeq_firstn:
  forall ta tb n (la: list ta) (lb: list tb),
    ta=tb -> JMeq la lb -> JMeq (firstn n la) (firstn n lb).
Proof.
intros. subst tb. apply JMeq_eq in H0. subst lb. auto.
Qed.

Lemma JMeq_length:
  forall ta tb (la: list ta) (lb: list tb),
     ta=tb -> JMeq la lb -> length la = length lb.
Proof.
intros. subst tb.  apply JMeq_eq in H0. subst lb. auto.
Qed.

Lemma JMeq_sublist:
  forall ta tb lo hi (la: list ta) (lb: list tb),
    ta=tb -> JMeq la lb -> JMeq (sublist lo hi la) (sublist lo hi lb).
Proof.
intros. subst tb. apply JMeq_eq in H0. subst lb. auto.
Qed.

 Definition fsig_of_funspec (fs: funspec)  :=  
  match fs with mk_funspec fsig _ _ _ => fsig end.

Lemma part1_splice_into_list:
  forall lo hi n al bl, 
    (0 <= lo <= Zlength bl)%Z ->
    sublist 0 lo (splice_into_list lo hi n al bl) = sublist 0 lo bl.
Proof.
 intros.
 unfold splice_into_list.
 rewrite (sublist_app 0 lo bl) by (rewrite ?Zlength_list_repeat, ?Z.max_l; omega).
rewrite ?Z.min_l by omega.
rewrite ?Z.max_r by omega.
rewrite sublist_nil, <- app_nil_end by omega.
 rewrite (sublist_app); rewrite ?Zlength_list_repeat, ?Z.max_l by omega; try omega;
 rewrite ?Zlength_sublist by omega;
 try (rewrite ?Zlength_correct; omega).
rewrite ?Z.min_l by omega.
rewrite ?Z.max_r by omega.
rewrite sublist_nil, <- app_nil_end by omega.
rewrite sublist_same; auto.
rewrite Zlength_sublist; omega.
Qed.

Lemma part3_splice_into_list:
  forall lo hi n al bl, 
    (0 <= lo <= hi)%Z -> (hi <= n)%Z ->
   (Zlength bl = n)%Z ->
   (Zlength al = hi-lo)%Z ->
    sublist hi n (splice_into_list lo hi n al bl) = sublist hi n bl.
Proof.
 intros.
 unfold splice_into_list.
 rewrite (sublist_app 0 lo bl) by (rewrite ?Zlength_list_repeat, ?Z.max_l; omega).
rewrite ?Z.min_l by omega.
rewrite ?Z.max_r by omega.
rewrite sublist_nil, <- app_nil_end by omega.
 rewrite (sublist_app 0 (hi-lo) al) by (rewrite ?Zlength_list_repeat, ?Z.max_r; omega).
rewrite ?Z.min_l by omega.
rewrite ?Z.max_r by omega.
rewrite sublist_nil, <- app_nil_end by omega.
rewrite (sublist_app hi n bl); try (rewrite ?Zlength_list_repeat, ?Z.max_r,  ?Z.max_l; omega).
rewrite ?Z.min_l by omega.
rewrite ?Z.max_r by omega.
rewrite sublist_nil, <- app_nil_end by omega.
rewrite <- app_ass.
 rewrite (sublist_app); rewrite ?Zlength_list_repeat, ?Z.max_r, ?Z.max_l by omega; try omega;
 rewrite ?Zlength_sublist by omega;
 try (rewrite ?Zlength_correct; omega).
rewrite !Zlength_app.
rewrite Zlength_sublist; try omega.
rewrite Zlength_sublist; try omega.
rewrite ?Z.min_r by omega.
rewrite ?Z.max_r by omega.
rewrite sublist_nil by omega.
simpl.
rewrite Z.max_l by omega.
rewrite sublist_sublist by omega.
f_equal. omega.
rewrite !Zlength_app.
rewrite !Zlength_sublist; omega.
Qed.

Lemma Zlength_splice_into_list:
  forall lo hi n al bl, 
    (0 <= lo <= hi)%Z -> (hi <= n)%Z ->
    Zlength (splice_into_list lo hi n al bl) = n.
Proof.
intros.
unfold splice_into_list.
rewrite !Zlength_app.
rewrite !Zlength_sublist; rewrite ?Zlength_app; rewrite ?Zlength_list_repeat; try omega.
destruct (zlt n (Zlength bl)).
rewrite Zmax_l by omega; omega.
rewrite Z.max_r; omega.
rewrite Z.max_r by omega.
rewrite Zlength_correct; omega.
destruct (zlt lo (Zlength bl)).
rewrite Zmax_l by omega; omega.
rewrite Z.max_r; omega.
Qed.

Local Arguments nested_field_type2 cs t gfs : simpl never.

(* Qinxiang:  look at the admits in this file.
 They are all about rerooting data_at and arrays.
*)

Lemma call_memcpy_tuchar:
  forall {cs: compspecs} (shp : share) (tp: type) (pathp: list gfield) (lop: Z) (vp': list val) (p: val)
           (shq: share) (tq: type) (pathq: list gfield) (loq: Z) (contents: list int) (q: val)
           (len : Z)
           (R': list (environ -> mpred))
           (np nq : Z)
           (vp vp'': reptype (nested_field_type2 tp pathp))
           (vq : reptype (nested_field_type2 tq pathq))
           (e_p e_q e_n : expr)
           Espec Delta P Q R,
      typeof e_p = tptr tuchar ->
      typeof e_q = tptr tuchar ->
      typeof e_n = tuint ->
      (var_types Delta) ! _memcpy = None ->
     (glob_specs Delta) ! _memcpy = Some (snd memcpy_spec) ->
     (glob_types Delta) ! _memcpy = Some (type_of_funspec (snd memcpy_spec)) ->
     writable_share shp ->  readable_share shq ->
     nested_field_type2 tp pathp = tarray tuchar np ->
     nested_field_type2 tq pathq = tarray tuchar nq ->
     (0 <= lop)%Z ->
     (0 <= len <= Int.max_unsigned)%Z ->
     (lop + len <= np)%Z ->
     (0 <= loq)%Z ->  (loq + len <=  (*Zlength contents <=*) nq)%Z ->
     JMeq vq (map Vint contents) ->
     JMeq vp vp' ->
     JMeq vp'' (splice_into_list lop (lop+len) np (sublist loq (Zlength contents) (map Vint contents)) vp') ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
         tc_exprlist Delta [tptr tvoid; tptr tvoid; tuint] [e_p; e_q; e_n]  &&         
         PROP () (LOCALx
                (`(eq (field_address0 tp (ArraySubsc lop :: pathp) p)) (eval_expr e_p) ::
                 `(eq (field_address0 tq (ArraySubsc loq :: pathq) q)) (eval_expr e_q) ::
                 `(eq (Vint (Int.repr len))) (eval_expr e_n) ::
                 Q)
         (SEPx (`(field_at shp tp pathp vp p) :: 
                   `(field_at shq tq pathq vq q) :: R'))) ->
   @semax cs Espec Delta 
    (PROPx P (LOCALx Q (SEPx R)))
    (Scall None
             (Evar _memcpy 
               (Tfunction
                (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                  (tptr tvoid) cc_default))
              [e_p; e_q; e_n])
    (normal_ret_assert (PROPx P (LOCALx Q 
     (SEPx (`(field_at shp tp pathp vp'' p) :: 
               `(field_at shq tq pathq vq q) :: R'))))).
Proof.
intros until R.
intros TCp TCq TCn Hvar Hspec Hglob ? SHq ? ? Hlop Hlen Hnp Hloq Hnq; intros.
assert_PROP (fold_right and True P); [ entailer | ].
apply semax_post' with
   (PROPx nil   (LOCALx Q
           (SEPx
              (`(field_at shp tp pathp vp'' p)
               :: `(field_at shq tq pathq vq q) :: R'))));
 [ entailer | ].
clear H6. rename H5 into Hpre.
assert_PROP (Zlength vp' = np /\ Zlength contents = nq). {
eapply derives_trans; [apply Hpre |].
apply andp_left2.
entailer. apply prop_right.
clear - H10 H12 H0 H1 H2 H3 H Hlop Hloq Hnp Hnq Hlen.
forget (nested_field_type2 tp pathp) as t0.
forget (nested_field_type2 tq pathq) as t1.
subst t0 t1.
simplify_value_fits in H10. destruct H10 as [H10 _].
simplify_value_fits in H12. destruct H12 as [H12 _].
apply JMeq_eq in H3. subst vp; auto.
apply JMeq_eq in H2. subst vq; auto.
rewrite Zlength_map in H12.
split; auto.
} destruct H5 as [Hvp' Hvq'].

assert (reptype (tarray tuchar np) = list val) by reflexivity.
rewrite <- H0 in H5.
assert (H99: reptype (nested_field_type2 tp (ArraySubsc 0 :: pathp)) = val).
 clear - H0. unfold nested_field_type2 in *; simpl in *.
  destruct (nested_field_rec tp pathp); inv H0. destruct p. subst.
 reflexivity.
assert (exists vpx : list (reptype (nested_field_type2 tp (ArraySubsc 0 :: pathp))),
                    JMeq vp vpx).
rewrite H99. rewrite <- H5. exists vp; auto.
destruct H6 as [vpx Hvpx].
assert_PROP (legal_nested_field tp pathp /\ legal_nested_field tq pathq). {
  eapply derives_trans; [apply Hpre | apply andp_left2]. 
entailer. apply prop_right. clear - H10 H12; hnf in H10,H12; intuition.
} destruct H6 as [LNFp LNFq].
erewrite field_at_Tarray in Hpre; try eassumption; auto; try omega.

assert (H98: reptype (nested_field_type2 tq (ArraySubsc 0 :: pathq)) = val).
 clear - H1. unfold nested_field_type2 in *; simpl in *.
  destruct (nested_field_rec tq pathq); inv H1. destruct p. subst.
 reflexivity.
assert (exists vqx : list (reptype (nested_field_type2 tq (ArraySubsc 0 :: pathq))),
                    JMeq vq vqx).
 rewrite H98. exists (map Vint contents); auto.
destruct H6 as [vqx Hvqx].
assert (JMeq vqx (map Vint contents)) by (etransitivity; try eassumption; auto).
assert (LENvqx: Zlength vqx = nq). {
clear - H98 H6 Hvq'.
transitivity (Zlength (map Vint contents)).
forget (map Vint contents) as l.
forget val as t. subst t. 
apply JMeq_eq in H6. subst; auto.
rewrite Zlength_map; auto.
}
assert (LENvpx: Zlength vpx = np). {
clear - H99 H5 H3 Hvp' Hvpx.
assert (JMeq vp' vpx) by (rewrite <- H3; auto).
clear Hvpx vp H3.
forget val as t. subst t.
apply JMeq_eq in H. subst; auto.
}
erewrite (field_at_Tarray shq) in Hpre|-*; try eassumption; auto; try omega.
rewrite (split2_array_at shp tp pathp 0 (lop+len)) in Hpre by omega.
rewrite (split2_array_at shp tp pathp 0 lop) in Hpre by omega.
rewrite (split2_array_at shq tq pathq 0 (loq+len)) in Hpre|-* by omega.
rewrite (split2_array_at shq tq pathq 0 loq (loq+len)) in Hpre|-* by omega.

rewrite !Z.sub_0_r in *.
rewrite Zlength_sublist in Hpre|-*; try omega.
rewrite Zlength_sublist in Hpre; try omega.
rewrite sublist_sublist in Hpre|-* by omega.
rewrite sublist_sublist in Hpre|-* by omega.
rewrite sublist_sublist in Hpre; try omega.
rewrite !Z.add_0_r in *.
rewrite !Z.sub_0_r in *.

normalize in Hpre. normalize.

pose (witness := ((shq,shp),
                              field_address0 tp (ArraySubsc lop :: pathp) p,
                              field_address0 tq (ArraySubsc loq :: pathq) q,
                              len,  sublist loq (loq+len) contents)).
pose (Frame := 
         `(array_at shp tp pathp 0 lop
              (sublist 0 lop vpx) p)
          :: `(array_at shp tp pathp (lop+len) np
                 (sublist (lop + len) (Zlength vpx) vpx) p)
             :: `(array_at shq tq pathq 0 loq (sublist 0 loq vqx) q) *
                `(array_at shq tq pathq (loq + len) nq
                    (sublist (loq+len) (Zlength vqx) vqx) q) :: R').
eapply semax_post_flipped'.
*
 eapply (semax_call_id0_alt _ _ _ _ _ _ _ _ _ _ _ witness Frame);
  try eassumption; try reflexivity.
 3: instantiate (1:= fst (fsig_of_funspec (snd memcpy_spec))); reflexivity.
 2: assumption.
 rewrite Hspec.
 f_equal. simpl @snd. simpl @fst.  f_equal. f_equal.
 reflexivity.
 reflexivity.
 eapply derives_trans; [apply Hpre | apply andp_left1]; auto.
 eapply derives_trans; [apply Hpre | apply andp_left2].
 clear Hpre.
 unfold Frame; go_lowerx.
 super_unfold_lift. 
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp.
 Focus 2. {
 unfold temp, make_args'.
 unfold_lift. simpl.
 unfold eval_id. simpl. rewrite <- H8, <- H9, <- H10.
 rewrite TCp, TCq, TCn.
 simpl.
 split.
 unfold field_address0.
 if_tac; [ |  reflexivity].
 destruct H12 as [? _]; destruct p; try contradiction; reflexivity.
 split.
 unfold field_address0.
 if_tac; [ |  reflexivity].
 destruct H12 as [? _]; destruct q; try contradiction; reflexivity.
 split; auto.
 } Unfocus.
 rewrite map_sublist.
 cancel.
 rewrite sepcon_comm.
 apply sepcon_derives.
 admit.
 admit.
*
 go_lowerx. unfold_lift.
 simpl.
 Intros x.
 normalize.
 rewrite map_sublist.
 cancel.
 clear witness Frame.
 hnf in H9. normalize in H9.
 subst x.
 simpl.
 clear Hpre H7 H8 P Q rho .
assert (exists (vpy : list (reptype (nested_field_type2 tp (ArraySubsc 0 :: pathp)))),
                  JMeq vp'' vpy)
  by (rewrite H99; eauto).
destruct H7 as [vpy H8].
assert (Zlength vpy = np). {
 assert (JMeq vpy  (splice_into_list lop (lop + len) np
          (sublist loq (Zlength contents) (map Vint contents)) vp')).
 rewrite <- H8. apply H4.
 transitivity (Zlength  (splice_into_list lop (lop + len) np
          (sublist loq (Zlength contents) (map Vint contents)) vp')).
 clear - H7 H99 H5.
 forget (splice_into_list lop (lop + len) np
          (sublist loq (Zlength contents) (map Vint contents)) vp') as vv.
 forget val as t. subst t. apply JMeq_eq in H7. subst; auto.
 rewrite Zlength_splice_into_list; try omega.
}
 erewrite field_at_Tarray; try eassumption; try omega.
 rewrite (split2_array_at shp tp pathp 0 lop np)  by omega.
 rewrite (split2_array_at shp tp pathp lop (lop+len) np)  by omega.
 rewrite Z.sub_0_r.
 replace (lop+len-lop)%Z with len by omega.
rewrite Zlength_sublist; try omega.
 rewrite sublist_sublist; try omega.
 rewrite sublist_sublist; try omega.
 rewrite Z.add_0_l.
 rewrite <- sepcon_assoc.
match goal with |- ?A * ?B * ?C * ?D |-- _ =>
 apply derives_trans with (C * B * D * A); [solve [cancel] | ]
end.
repeat apply sepcon_derives.
+
 apply array_at_ext_derives.
 rewrite !Zlength_sublist; omega.
 intros.
 replace u0 with u1; auto.
 forget  (default_val (nested_field_type2 tp (ArraySubsc 0 :: pathp))) as d.
 apply JMeq_eq.
 rewrite H10,H11. clear u0 u1 H10 H11.
 rewrite Z.sub_0_r.
 admit.  (* tedious *)
+
  admit.
+ 
 apply array_at_ext_derives.
 rewrite !Zlength_sublist; omega.
 intros.
 replace u0 with u1; auto.
 forget  (default_val (nested_field_type2 tp (ArraySubsc 0 :: pathp))) as d.
 apply JMeq_eq.
 rewrite H10,H11. clear u0 u1 H10 H11.
  rewrite (Z.add_comm len lop).
  rewrite Z.sub_add.
 admit.  (* tedious *)
+
  admit.
Qed.

Lemma call_memset_tuchar:
  forall {cs: compspecs} (shp : share) (tp: type) (pathp: list gfield) (lop: Z) (vp': list val) (p: val)
           (c: int) (len : Z)
           (R': list (environ -> mpred))
           (np : Z)
           (vp vp'': reptype (nested_field_type2 tp pathp))
           (e_p e_c e_n : expr)
           Espec Delta P Q R (s: signedness) 
   (TCp : typeof e_p = tptr tuchar)
   (TCc : typeof e_c = tint)
   (TCn : typeof e_n = Tint I32 s noattr)
   (Hvar : (var_types Delta) ! _memset = None)
   (Hspec : (glob_specs Delta) ! _memset = Some (snd memset_spec))
   (Hglob : (glob_types Delta) ! _memset =
        Some (type_of_funspec (snd memset_spec)))
   (H:  writable_share shp)
   (Hlop : (0 <= lop)%Z)
   (Hlen: (0 <= len <= Int.max_unsigned)%Z)
   (H0:  nested_field_type2 tp pathp = tarray tuchar np)
(*   (Hvp' : (lop <= Zlength vp' <= np)%Z)*)
   (Hnp : (lop + len <= np)%Z)
   (H3:  JMeq vp vp')
   (H4:  JMeq vp'' (splice_into_list lop (lop+len) np (list_repeat (Z.to_nat len) (Vint c)) vp'))
   (H5: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
         tc_exprlist Delta [tptr tvoid; tint; tuint] [e_p; e_c; e_n] &&                 
         PROP () (LOCALx
                (`(eq (field_address0 tp (ArraySubsc lop :: pathp) p)) (eval_expr e_p) ::
                 `(eq (Vint c)) (eval_expr e_c) ::
                 `(eq (Vint (Int.repr len))) (eval_expr e_n) ::
                 Q)
         (SEPx (`(field_at shp tp pathp vp p) :: R')))),
   @semax cs Espec Delta 
    (PROPx P (LOCALx Q (SEPx R)))
    (Scall None
             (Evar _memset 
               (Tfunction
                (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                  (tptr tvoid) cc_default))
              [e_p; e_c; e_n])
    (normal_ret_assert (PROPx P (LOCALx Q 
     (SEPx (`(field_at shp tp pathp vp'' p) :: R'))))).
Proof.
intros.
assert_PROP (fold_right and True P); [ entailer | ].
apply semax_post' with
   (PROPx nil   (LOCALx Q
           (SEPx (`(field_at shp tp pathp vp'' p) :: R'))));
 [ entailer | ].
rename H5 into Hpre.
clear H1.
assert_PROP (Zlength vp' = np). {
eapply derives_trans; [apply Hpre | apply andp_left2].
entailer. apply prop_right.
clear - H8 H4 H3 Hnp H0 Hlen Hlop.
forget (nested_field_type2 tp pathp) as t0.
subst t0.
simplify_value_fits in H8. destruct H8 as [H8 _].
apply JMeq_eq in H3. subst vp; auto.
} rename H1 into Hvp'.
assert (H5: reptype (tarray tuchar np) = list val) by reflexivity.
rewrite <- H0 in H5.
assert (H99: reptype (nested_field_type2 tp (ArraySubsc 0 :: pathp)) = val).
 clear - H0. unfold nested_field_type2 in *; simpl in *.
  destruct (nested_field_rec tp pathp); inv H0. destruct p. subst.
 reflexivity.
assert (H6: exists vpx : list (reptype (nested_field_type2 tp (ArraySubsc 0 :: pathp))),
                    JMeq vp' vpx).
rewrite H99. eauto.
destruct H6 as [vpx Hvpx].
assert_PROP (legal_nested_field tp pathp). {
  eapply derives_trans; [apply Hpre | apply andp_left2]. 
entailer. apply prop_right. clear - H8; hnf in H8; intuition.
} rename H1 into LNFp.
rewrite Hvpx in H3.
assert (LENvpx: Zlength vpx = np). {
clear - H99 Hvp' Hvpx.
forget val as t. subst t.
apply JMeq_eq in Hvpx. subst; auto.
}
erewrite field_at_Tarray in Hpre; try eassumption; auto; try omega.
rewrite (split2_array_at shp tp pathp 0 (lop+len)) in Hpre by omega.
rewrite (split2_array_at shp tp pathp 0 lop) in Hpre by omega.
rewrite Zlength_sublist in Hpre; try omega.
rewrite sublist_sublist in Hpre by omega.
rewrite sublist_sublist in Hpre by omega.
rewrite !Z.sub_0_r in Hpre.
rewrite !Z.add_0_r in Hpre.

pose (witness := (shp,
                              field_address0 tp (ArraySubsc lop :: pathp) p,
                              len,  c)).
pose (Frame := 
         `(array_at shp tp pathp (lop + len) np
              (sublist (lop+len) np vpx) p)
          :: `(array_at shp tp pathp 0 lop (sublist 0 lop vpx) p)
              :: R').
eapply semax_post_flipped'.
*
 eapply (semax_call_id0_alt _ _ _ _ _ _ _ _ _ _ _ witness Frame);
  try eassumption; try reflexivity.
 3: instantiate (1:= fst (fsig_of_funspec (snd memset_spec))); reflexivity.
 2: assumption.
 rewrite Hspec.
 f_equal. simpl @snd. simpl @fst.  f_equal. f_equal.
 reflexivity.
 reflexivity.
 eapply derives_trans; [apply Hpre | apply andp_left1]; auto.
 eapply derives_trans; [apply Hpre | apply andp_left2].
 clear Hpre.
 pose (H6 := True).
 pose (H2 := True).
 pose (H1 := True).
 unfold Frame; go_lowerx.
 replace (lop+len-lop)%Z with len by omega.
 super_unfold_lift.
 simpl.
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp.
 Focus 2. {
 unfold temp, make_args'.
 unfold_lift. simpl.
 unfold eval_id. simpl. rewrite <- H8, <- H9, <- H10.
 rewrite TCp, TCc, TCn.
 simpl.
 split.
 unfold field_address0.
 if_tac; [ |  reflexivity].
 destruct H12 as [? _]; destruct p; try contradiction; reflexivity.
 auto.
 } Unfocus.
 rewrite LENvpx.
 cancel.
 admit.  (* array_at -> memory_block *)
*
 go_lowerx. unfold_lift; simpl. 
 Intros x.
 normalize.
 cancel.
 clear witness Frame.
 hnf in H6. normalize in H6.
 subst x. clear dependent rho. clear H1 Hpre.
 assert (H2: exists (vpy : list (reptype (nested_field_type2 tp (ArraySubsc 0 :: pathp)))),
                  JMeq vp'' vpy).
 rewrite H99. eauto.
destruct H2 as [vpy H8].
erewrite field_at_Tarray; try eassumption; auto; try omega.
rewrite H4 in H8.
clear dependent vp''. clear dependent e_c. clear dependent e_p. clear dependent e_n.
clear dependent Delta.
assert (Zlength vpy = np). {
clear - H0 H8 Hvp' Hnp Hlop Hlen.
generalize dependent vpy.
rewrite nested_field_type2_ind, H0. simpl. rewrite reptype_ind; simpl.
intros.
subst.
clear H0.
rewrite Zlength_splice_into_list by omega.
auto.
}
rewrite (split2_array_at shp tp pathp 0 (lop+len) np) by omega.
rewrite (split2_array_at shp tp pathp 0 lop (lop+len)) by omega.
rewrite !Z.sub_0_r.
rewrite Zlength_sublist by omega.
rewrite sublist_sublist by omega.
rewrite sublist_sublist by omega.
rewrite !Z.sub_0_r.
rewrite !Z.add_0_r.
rewrite H1.
replace (sublist 0 lop vpx) with (sublist 0 lop vpy).
Focus 2. {
generalize dependent vpy.
generalize dependent vpx.
rewrite H99.
intros.
apply JMeq_eq in H8. apply JMeq_eq in Hvpx.
subst.
apply part1_splice_into_list; omega.
} Unfocus.
replace (sublist (lop+len) np vpx) with (sublist (lop+len) np vpy).
Focus 2. {
generalize dependent vpy.
generalize dependent vpx.
rewrite H99.
intros.
apply JMeq_eq in H8. apply JMeq_eq in Hvpx.
subst.
apply part3_splice_into_list; try omega.
rewrite Zlength_list_repeat. rewrite Z.max_r by omega. omega.
} Unfocus.
cancel.
admit.
Qed.

