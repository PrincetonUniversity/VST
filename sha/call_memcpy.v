Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import JMeq.
Local Open Scope nat.
Local Open Scope logic.

Definition splice_into_list (lo hi n : Z) (source target : list val) : list val :=
   firstn (Z.to_nat lo) (target ++ list_repeat (Z.to_nat (lo - Zlength target)) Vundef)
   ++ firstn (Z.to_nat (hi-lo)) (source ++ list_repeat (Z.to_nat (hi-lo)) Vundef)
   ++ firstn (Z.to_nat (n-hi)) (skipn (Z.to_nat hi) (target ++ list_repeat (Z.to_nat (n- Zlength target)) Vundef)).

Lemma splice_into_list_simplify0:
  forall n src dst, 
    Zlength src = n ->
    Zlength dst = n ->
    splice_into_list 0 n n src dst = src.
Proof.
 intros.
 unfold splice_into_list.
 rewrite Z.sub_0_r. change (Z.of_nat 0) with 0%nat.
 simpl firstn. unfold app at 1.
 rewrite firstn_app1.
 rewrite Z.sub_diag. change (Z.to_nat 0) with 0. simpl firstn. 
 rewrite firstn_same. rewrite <- app_nil_end; auto.
 rewrite <- H. rewrite Zlength_correct. rewrite Nat2Z.id; auto.
 rewrite <- H. rewrite Zlength_correct. rewrite Nat2Z.id; auto.
Qed.

Lemma splice_into_list_simplify1:
  forall lo hi src tgt,
    lo = Zlength tgt ->
    (hi-lo = Zlength src)%Z ->
    splice_into_list lo hi hi src tgt = tgt++src.
Proof.
intros; subst; unfold splice_into_list.
rewrite H0.
rewrite Z.sub_diag.
change (Z.to_nat 0) with 0.
unfold list_repeat at 1.
repeat rewrite ZtoNat_Zlength.
rewrite <- app_nil_end.
rewrite firstn_same by omega.
f_equal.
rewrite firstn_app1 by omega.
rewrite firstn_same by omega.
pose proof (Zlength_nonneg src).
pose proof (Zlength_nonneg tgt).
pose proof (skipn_length_short (Z.to_nat hi) tgt).
spec H2.
apply Nat2Z.inj_le.
rewrite <- Zlength_correct.
rewrite Z2Nat.id by omega.
omega.
destruct (skipn (Z.to_nat hi) tgt); inv H2.
rewrite Z.sub_diag.
change (Z.to_nat 0) with 0.
simpl. rewrite <- app_nil_end; auto.
Qed.

Lemma splice_into_list_simplify2:
  forall lo hi src tgt,
    lo = Zlength tgt ->
    (lo <= hi)%Z ->
    (hi-lo <= Zlength src)%Z ->
    splice_into_list lo hi hi src tgt = tgt++ firstn (Z.to_nat (hi-lo)) src.
Proof.
intros; subst; unfold splice_into_list.
repeat rewrite Z.sub_diag.
change (Z.to_nat 0) with 0.
unfold list_repeat at 1.
repeat rewrite ZtoNat_Zlength.
rewrite <- app_nil_end.
rewrite firstn_same by omega.
f_equal.
pose proof (Zlength_nonneg src).
pose proof (Zlength_nonneg tgt).
rewrite skipn_short.
rewrite <- app_nil_end.
rewrite firstn_app1; auto.
apply Nat2Z.inj_le.
rewrite <- Zlength_correct.
rewrite Z2Nat.id by omega.
auto.
rewrite app_length.
rewrite length_list_repeat.
rewrite <- (Nat2Z.id (length tgt)).
rewrite <- Zlength_correct. 
rewrite <- Z2Nat.inj_add by omega.
unfold ge.
rewrite <- Z2Nat.inj_le; try omega.
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

 Definition fsig_of_funspec (fs: funspec)  :=  
  match fs with mk_funspec fsig _ _ _ => fsig end.

Lemma firstn_splice_into_list:
  forall lo hi n al bl, 
    (0 <= lo <= Zlength bl)%Z ->
    firstn (Z.to_nat lo) (splice_into_list lo hi n al bl) = firstn (Z.to_nat lo) bl.
Proof.
 intros.
 assert (Z.to_nat lo <= length bl).
 destruct H;  apply Z2Nat.inj_le in H0; try omega.
 rewrite Zlength_correct in H0.
 rewrite Nat2Z.id in H0; auto.
 unfold splice_into_list.
 rewrite firstn_app1.
 pattern (Z.to_nat lo) at 2;  replace (Z.to_nat lo) with (Z.to_nat lo + 0) by omega.
 rewrite firstn_firstn.
 rewrite firstn_app1; auto.
 rewrite firstn_app1; auto.
 rewrite firstn_length, min_l; auto.
Qed. 


Lemma length_splice_into_list:
  forall lo hi n al bl, 
    (0 <= lo <= hi)%Z -> (hi <= n)%Z ->
    Zlength (splice_into_list lo hi n al bl) = n.
Proof.
intros.
unfold splice_into_list.
rewrite Zlength_correct.
repeat rewrite app_length.
rewrite firstn_length, min_l.
rewrite firstn_length, min_l.
rewrite firstn_length, min_l.
rewrite <- Z2Nat.inj_add; try omega.
rewrite <- Z2Nat.inj_add; try omega.
rewrite Z2Nat.id; try omega.
rewrite skipn_length.
destruct (zlt n (Zlength bl)).
rewrite (Z2Nat_nonpos_0 (n - Zlength bl)) by omega.
unfold list_repeat; simpl; rewrite <- app_nil_end.
rewrite <- (Nat2Z.id (length bl)).
rewrite <- Zlength_correct.
rewrite <- Z2Nat.inj_sub by omega.
   apply Z2Nat.inj_le; omega.
rewrite app_length.
rewrite length_list_repeat.
rewrite Z2Nat.inj_sub by omega.
rewrite <- (Nat2Z.id (length bl)).
rewrite <- Zlength_correct.
rewrite <- Z2Nat.inj_sub by omega.
rewrite <- Z2Nat.inj_add; try omega.
rewrite <- Z2Nat.inj_sub by omega.
   apply Z2Nat.inj_le; omega.
apply Zlength_nonneg.
rewrite app_length.
rewrite length_list_repeat.
omega.
rewrite app_length.
rewrite length_list_repeat.
rewrite <- (Nat2Z.id (length bl)).
rewrite <- Zlength_correct.
destruct (zlt lo (Zlength bl)).
rewrite (Z2Nat_nonpos_0 (_ - _)) by omega.
rewrite NPeano.Nat.add_0_r.
   apply Z2Nat.inj_le; omega.
rewrite <- Z2Nat.inj_add; try omega.
   apply Z2Nat.inj_le; omega.
apply Zlength_nonneg.
Qed.

Lemma call_memcpy_tuchar:
  forall (shp : share) (tp: type) (pathp: list gfield) (lop: Z) (vp': list val) (p: val)
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
     writable_share shp ->
     nested_field_type2 tp pathp = tarray tuchar np ->
     nested_field_type2 tq pathq = tarray tuchar nq ->
     (0 <= lop)%Z -> (0 <= len <= Int.max_unsigned)%Z ->
     (lop <= Zlength vp' <= np)%Z ->
     (lop + len <= np)%Z ->
     (0 <= loq)%Z ->  (loq + len <=  Zlength contents <= nq)%Z ->
     JMeq vq (map Vint contents) ->
     JMeq vp vp' ->
     JMeq vp'' (splice_into_list lop (lop+len) np (skipn (Z.to_nat loq) (map Vint contents)) vp') ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
         PROP () (LOCALx
                (tc_exprlist Delta [tptr tvoid; tptr tvoid; tuint] [e_p; e_q; e_n] ::
                 `(eq (field_address0 tp (ArraySubsc lop :: pathp) p)) (eval_expr e_p) ::
                 `(eq (field_address0 tq (ArraySubsc loq :: pathq) q)) (eval_expr e_q) ::
                 `(eq (Vint (Int.repr len))) (eval_expr e_n) ::
                 Q)
         (SEPx (`(field_at shp tp pathp vp p) :: 
                   `(field_at shq tq pathq vq q) :: R'))) ->
   @semax Espec Delta 
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
intros TCp TCq TCn Hvar Hspec Hglob ? ? ? Hlop Hlen Hvp' Hnp Hloq Hnq; intros.
assert_PROP (fold_right and True P); [ entailer | ].
eapply semax_pre; [ eassumption | ].
apply semax_post' with
   (PROPx nil   (LOCALx Q
           (SEPx
              (`(field_at shp tp pathp vp'' p)
               :: `(field_at shq tq pathq vq q) :: R'))));
 [ entailer | ].
clear H5 H6 P R.
assert (He: exists (vpe: reptype (nested_field_type2 tp pathp)),
               JMeq vpe (vp' ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef)).
 rewrite H0.
 econstructor. apply eq_JMeq. reflexivity.
destruct He as [vpe He].
rewrite (field_at_data_equal shp tp pathp vp vpe).
Focus 2. {
eapply (data_equal_JMeq (tarray tuchar np)); auto.
symmetry; apply H3.
symmetry; apply He.
apply data_equal_list_repeat_default.
} Unfocus.
assert (reptype (tarray tuchar np) = list val) by reflexivity.
rewrite <- H0 in H5.
assert (H99: reptype (nested_field_type2 tp (ArraySubsc 0 :: pathp)) = val).
 clear - H0. unfold nested_field_type2 in *; simpl in *.
  destruct (nested_field_rec tp pathp); inv H0. destruct p. subst.
 reflexivity.
assert (exists vpx : list (reptype (nested_field_type2 tp (ArraySubsc 0 :: pathp))),
                    JMeq vpe vpx).
rewrite H99. rewrite <- H5. exists vpe; auto.
destruct H6 as [vpx Hvpx].
rewrite (array_seg_reroot_lemma shp tp pathp tuchar np
              noattr lop (lop+len) (firstn (Z.to_nat lop) vpx)
                  (firstn (Z.to_nat len) (skipn (Z.to_nat lop) vpx))
                  (skipn (Z.to_nat lop + Z.to_nat len) vpx)
                  (firstn (Z.to_nat len) (skipn (Z.to_nat lop)
                              (vp'  ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef)))
                  ); auto; try omega.
2: apply JMeq_firstn; auto ; apply JMeq_skipn; auto.
2:  apply JMeq_trans with (y:= vpe); auto.
Focus 2. {
 apply JMeq_trans with (y:= vpx); auto.
 rewrite <- skipn_skipn.
 rewrite firstn_skipn. rewrite firstn_skipn. auto.
} Unfocus.
Focus 2.  {
rewrite Zlength_correct. rewrite firstn_length. rewrite min_l.
rewrite Z2Nat.id by omega; auto.
apply le_trans with (length vp').
rewrite <- (Nat2Z.id (length vp')).
apply Z2Nat.inj_le; try omega. rewrite <- Zlength_correct; omega.
clear - Hvpx He H99.
replace (length vpx) with (length (vp' ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef)).
rewrite app_length; omega.
apply JMeq_length; auto.
apply JMeq_trans with (y:=vpe); auto.
} Unfocus.
Focus 2. {
rewrite Zlength_correct.
rewrite firstn_length. rewrite min_l. rewrite Z2Nat.id by omega. omega.
rewrite skipn_length.
replace (length vpx) with (Z.to_nat (Zlength (vp' ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef))).
rewrite <- Z2Nat.inj_sub by omega.
apply Z2Nat.inj_le; try omega.
rewrite Zlength_app.
rewrite (Zlength_correct (list_repeat _ _)). omega.
rewrite Zlength_app. 
rewrite (Zlength_correct (list_repeat _ _)).
rewrite length_list_repeat.
destruct (zlt (lop+len) (Zlength vp') ).
omega.
rewrite Z2Nat.id; try omega.
rewrite Zlength_correct. rewrite Nat2Z.id.
apply JMeq_length; auto.
apply JMeq_trans with (y:=vpe); auto.
} Unfocus.
assert (H98: reptype (nested_field_type2 tq (ArraySubsc 0 :: pathq)) = val).
 clear - H1. unfold nested_field_type2 in *; simpl in *.
  destruct (nested_field_rec tq pathq); inv H1. destruct p. subst.
 reflexivity.
assert (exists vqx : list (reptype (nested_field_type2 tq (ArraySubsc 0 :: pathq))),
                    JMeq vq vqx).
 rewrite H98. exists (map Vint contents); auto.
destruct H6 as [vqx Hvqx].
assert (JMeq vqx (map Vint contents)) by (etransitivity; try eassumption; auto).
rewrite (array_seg_reroot_lemma shq tq pathq tuchar nq
              noattr loq (loq+len) (firstn (Z.to_nat loq) vqx)
                  (firstn (Z.to_nat len) (skipn (Z.to_nat loq) vqx))
                  (skipn (Z.to_nat loq + Z.to_nat len) vqx)
                  (firstn (Z.to_nat len) (skipn (Z.to_nat loq) (map Vint contents)))
                  ); auto; try omega.
2: apply JMeq_firstn; auto; apply JMeq_skipn; auto.
2: eapply JMeq_trans; [ | symmetry; eassumption];
  rewrite <- skipn_skipn, firstn_skipn, firstn_skipn; reflexivity.
Focus 2.  {
rewrite Zlength_correct. rewrite firstn_length. rewrite min_l.
rewrite Z2Nat.id by omega; auto.
replace (length vqx) with (length (map Vint contents)).
rewrite <- (Nat2Z.id (length (map Vint contents))).
apply Z2Nat.inj_le; try omega. rewrite map_length, <- Zlength_correct; omega.
apply JMeq_length; auto.
} Unfocus.
Focus 2. {
rewrite Zlength_correct.
rewrite firstn_length. rewrite min_l. rewrite Z2Nat.id by omega. omega.
rewrite skipn_length.
replace (length vqx) with (Z.to_nat (Zlength (map Vint contents))).
rewrite <- Z2Nat.inj_sub by omega.
rewrite Zlength_map.
apply Z2Nat.inj_le; omega. 
rewrite Zlength_correct. rewrite Nat2Z.id.
apply JMeq_length; auto.
} Unfocus.

normalize.
rewrite sepcon_assoc.
rewrite <- sepcon_comm.
rewrite flatten_sepcon_in_SEP.
rewrite flatten_sepcon_in_SEP.
pose (witness := ((shq,shp),
                              field_address0 tp (ArraySubsc lop :: pathp) p,
                              field_address0 tq (ArraySubsc loq :: pathq) q,
                              len,  (firstn (Z.to_nat len)
                 (skipn (Z.to_nat loq) contents)))).
pose (Frame := 
         `(array_at shp tp pathp (lop + len) np
              (skipn (Z.to_nat lop + Z.to_nat len) vpx) p)
          :: `(array_at shp tp pathp 0 lop (firstn (Z.to_nat lop) vpx) p)
             :: `(array_at shq tq pathq 0 loq (firstn (Z.to_nat loq) vqx) q) *
                `(array_at shq tq pathq (loq + len) nq
                    (skipn (Z.to_nat loq + Z.to_nat len) vqx) q) :: R').
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
 unfold Frame; go_lowerx.
 replace (lop+len-lop)%Z with len by omega.
 replace (loq+len-loq)%Z with len by omega.
 super_unfold_lift.
 simpl.
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp.
 Focus 2. {
 unfold temp, make_args'.
 unfold_lift. simpl.
 unfold eval_id. simpl. rewrite <- H10, <- H11, <- H12.
 rewrite TCp, TCq, TCn.
 simpl.
 split.
 unfold field_address0.
 if_tac; [ |  reflexivity].
 destruct H14 as [? _]; destruct p; try contradiction; reflexivity.
 split.
 unfold field_address0.
 if_tac; [ |  reflexivity].
 destruct H14 as [? _]; destruct q; try contradiction; reflexivity.
 split; auto.
 } Unfocus.
 rewrite map_firstn, <- skipn_map.
 cancel.
*
 go_lowerx.
 normalize.
 replace (loq+len-loq)%Z with len by omega.
 rewrite map_firstn, <- skipn_map.
 cancel.
clear witness Frame.
 hnf in H13. normalize in H13.
 subst x. clear H10 H11 H12 H9 H8 H7 rho.
assert (exists (vpy : list (reptype (nested_field_type2 tp (ArraySubsc 0 :: pathp)))),
                  JMeq vpy vp'').
 rewrite H99. eauto.
destruct H7 as [vpy H8].
rewrite (array_seg_reroot_lemma shp tp pathp tuchar np
              noattr lop (lop+len) (firstn (Z.to_nat lop) vpy)
                  (firstn (Z.to_nat len) (skipn (Z.to_nat lop) vpy))
                  (skipn (Z.to_nat lop + Z.to_nat len) vpy)
                  (firstn (Z.to_nat len) (skipn (Z.to_nat loq) (map Vint contents)))
                  ); auto; try omega.
+ replace (lop+len-lop)%Z with len by omega.
    replace (firstn (Z.to_nat lop) vpx) with (firstn (Z.to_nat lop) vpy).
    replace (skipn (Z.to_nat lop + Z.to_nat len) vpx) 
     with (skipn (Z.to_nat lop + Z.to_nat len) vpy).
    cancel.
    rewrite <- Z2Nat.inj_add; try omega.
    clear - H8 H4 He Hvpx H99 Hlop Hvp' Hnp Hlen.
    apply JMeq_eq.
    apply JMeq_trans 
      with (y:= skipn (Z.to_nat (lop + len)) (splice_into_list lop (lop + len) np
          (skipn (Z.to_nat loq) (map Vint contents)) vp')).
   apply JMeq_skipn; auto. eapply JMeq_trans; try eassumption.
    apply JMeq_trans 
      with (y:= skipn (Z.to_nat (lop + len)) (vp' ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef)).
   apply eq_JMeq.
   forget (skipn (Z.to_nat loq) (map Vint contents)) as bl.
   { clear - Hlop Hlen Hvp' Hnp.
     assert (Z.to_nat lop <= length vp').
       rewrite <- (Nat2Z.id (length vp')), <- Zlength_correct.
       apply Z2Nat.inj_le; omega.
     assert (Z.to_nat len =
                   length (firstn (Z.to_nat len) (bl ++ list_repeat (Z.to_nat len) Vundef))).
       rewrite firstn_length, min_l; auto .
       rewrite app_length, length_list_repeat. omega.
     unfold splice_into_list.
     rewrite firstn_app1 by auto.
     replace (lop+len-lop)%Z with len by omega.
     rewrite Z2Nat.inj_add by omega.
     repeat rewrite <- skipn_skipn.
     rewrite skipn_app1 by (rewrite firstn_length, min_l; omega).
     rewrite (skipn_short (Z.to_nat lop))  by (rewrite firstn_length, min_l; omega).
     simpl app.
     rewrite (skipn_app1 _ (Z.to_nat lop) vp') by auto.
     rewrite skipn_app1 by omega.
     rewrite skipn_short by omega.
     simpl.
     rewrite firstn_same; auto.
     rewrite skipn_length.
     rewrite app_length, length_list_repeat.
     rewrite skipn_length.
     rewrite <- (Nat2Z.id (length vp')), <- Zlength_correct.
     rewrite <- Z2Nat.inj_sub by omega.
     rewrite <- Z2Nat.inj_add by omega.
     rewrite <- Z2Nat.inj_sub by omega.
     apply Z2Nat.inj_le; omega.
   }
   apply JMeq_skipn; auto.
   apply JMeq_trans with (y := vpe); auto.
 assert (0 <= lop <= Zlength vp')%Z by omega.
   apply JMeq_eq.
 apply JMeq_trans with (y:= firstn (Z.to_nat lop)  (splice_into_list lop (lop + len) np
          (skipn (Z.to_nat loq) (map Vint contents)) vp')).
 apply JMeq_firstn; auto. eapply JMeq_trans; try eassumption.
 apply JMeq_trans with (y := firstn (Z.to_nat lop) (vp' ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef)).
  apply eq_JMeq.
 rewrite firstn_splice_into_list; auto.
 rewrite firstn_app1; auto.
 rewrite <- (Nat2Z.id (length vp')). rewrite <- Zlength_correct.
   apply Z2Nat.inj_le; omega.
 apply JMeq_firstn; auto.
 apply JMeq_trans with (y := vpe); auto.  
+  
   apply JMeq_trans with (y:=   firstn (Z.to_nat len) (skipn (Z.to_nat lop) (splice_into_list lop (lop + len) np
          (skipn (Z.to_nat loq) (map Vint contents)) vp'))).
  apply JMeq_firstn; auto. apply JMeq_skipn; auto. eapply JMeq_trans; eassumption.
  apply eq_JMeq.
assert (Z.to_nat len <= length (skipn (Z.to_nat loq) (map Vint contents))). {
 rewrite skipn_length. rewrite map_length. 
 destruct Hnq as [Hn ?].  clear - Hn Hloq Hlen.
 rewrite <- (Nat2Z.id (length contents)).
  rewrite <- Z2Nat.inj_sub; try omega.
 rewrite <- Zlength_correct. apply Z2Nat.inj_le; omega.
}
 unfold splice_into_list.
 rewrite skipn_app2.
 rewrite firstn_length, min_l. rewrite minus_diag. rewrite skipn_0.
 replace (lop+len-lop)%Z with len by omega.
 rewrite firstn_app1.
 rewrite firstn_app1 by auto.
 pattern (Z.to_nat len) at 2;  replace (Z.to_nat len) with (Z.to_nat len + 0) by omega.
 rewrite firstn_firstn.
 auto.
 rewrite firstn_app1 by auto.
 rewrite firstn_length, min_l; try omega.
 rewrite app_length.
 rewrite length_list_repeat.
 rewrite <- (Nat2Z.id (length vp')). rewrite <- Zlength_correct.
 destruct (zlt lop (Zlength vp')).
 apply Z2Nat.inj_lt in l; try omega.
  rewrite <- Z2Nat.inj_add; try omega.
 apply Z2Nat.inj_le; try omega.
 rewrite firstn_app1.
 rewrite firstn_length. rewrite min_l; try omega.
 rewrite <- (Nat2Z.id (length vp')). rewrite <- Zlength_correct.
 apply Z2Nat.inj_le; try omega.
 rewrite <- (Nat2Z.id (length vp')). rewrite <- Zlength_correct.
 apply Z2Nat.inj_le; try omega.
+
 rewrite <- skipn_skipn.
 rewrite firstn_skipn. rewrite firstn_skipn. auto.
+
 rewrite Zlength_correct, firstn_length, min_l.
 apply Z2Nat.id. omega.
 transitivity (length   (splice_into_list lop (lop + len) np
          (skipn (Z.to_nat loq) (map Vint contents)) vp')).
 rewrite <- (Nat2Z.id (length _)). rewrite <- Zlength_correct. 
 rewrite length_splice_into_list; try omega.
 apply Z2Nat.inj_le; try omega.
 apply NPeano.Nat.eq_le_incl.
 apply JMeq_length; auto.
 apply JMeq_trans with (y:=vp''); auto.
+
 rewrite Zlength_correct. rewrite firstn_length, min_l. rewrite Z2Nat.id by omega. omega.
 rewrite skipn_length.
 replace (length vpy) with (length (splice_into_list lop (lop + len) np
          (skipn (Z.to_nat loq) (map Vint contents)) vp'))
  by (apply JMeq_length; auto; apply JMeq_trans with (y:=vp''); auto).
 rewrite <- (Nat2Z.id (length _)). rewrite <- Zlength_correct. 
 rewrite length_splice_into_list; try omega.
 rewrite <- Z2Nat.inj_sub by omega.
 apply Z2Nat.inj_le; omega.
Qed.

Lemma call_memset_tuchar:
  forall (shp : share) (tp: type) (pathp: list gfield) (lop: Z) (vp': list val) (p: val)
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
   (Hvp' : (lop <= Zlength vp' <= np)%Z)
   (Hnp : (lop + len <= np)%Z)
   (H3:  JMeq vp vp')
   (H4:  JMeq vp'' (splice_into_list lop (lop+len) np (list_repeat (Z.to_nat len) (Vint c)) vp'))
   (H5: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
         PROP () (LOCALx
                (tc_exprlist Delta [tptr tvoid; tint; tuint] [e_p; e_c; e_n] ::
                 `(eq (field_address0 tp (ArraySubsc lop :: pathp) p)) (eval_expr e_p) ::
                 `(eq (Vint c)) (eval_expr e_c) ::
                 `(eq (Vint (Int.repr len))) (eval_expr e_n) ::
                 Q)
         (SEPx (`(field_at shp tp pathp vp p) :: R')))),
   @semax Espec Delta 
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
eapply semax_pre; [ eassumption | ].
apply semax_post' with
   (PROPx nil   (LOCALx Q
           (SEPx (`(field_at shp tp pathp vp'' p) :: R'))));
 [ entailer | ].
clear H5 H1 P R.
assert (He: exists (vpe: reptype (nested_field_type2 tp pathp)),
               JMeq vpe (vp' ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef)).
 rewrite H0.
 econstructor. apply eq_JMeq. reflexivity.
destruct He as [vpe He].
rewrite (field_at_data_equal shp tp pathp vp vpe).
Focus 2. {
eapply (data_equal_JMeq (tarray tuchar np)); auto.
symmetry; apply H3.
symmetry; apply He.
apply data_equal_list_repeat_default.
} Unfocus.
assert (H5: reptype (tarray tuchar np) = list val) by reflexivity.
rewrite <- H0 in H5.
assert (H99: reptype (nested_field_type2 tp (ArraySubsc 0 :: pathp)) = val).
 clear - H0. unfold nested_field_type2 in *; simpl in *.
  destruct (nested_field_rec tp pathp); inv H0. destruct p. subst.
 reflexivity.
assert (H6: exists vpx : list (reptype (nested_field_type2 tp (ArraySubsc 0 :: pathp))),
                    JMeq vpe vpx).
rewrite H99. rewrite <- H5. exists vpe; auto.
destruct H6 as [vpx Hvpx].
rewrite (array_seg_reroot_lemma shp tp pathp tuchar np
              noattr lop (lop+len) (firstn (Z.to_nat lop) vpx)
                  (firstn (Z.to_nat len) (skipn (Z.to_nat lop) vpx))
                  (skipn (Z.to_nat lop + Z.to_nat len) vpx)
                  (firstn (Z.to_nat len) (skipn (Z.to_nat lop)
                              (vp'  ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef)))
                  ); auto; try omega.
2: apply JMeq_firstn; auto ; apply JMeq_skipn; auto.
2:  apply JMeq_trans with (y:= vpe); auto.
Focus 2. {
 apply JMeq_trans with (y:= vpx); auto.
 rewrite <- skipn_skipn.
 rewrite firstn_skipn. rewrite firstn_skipn. auto.
} Unfocus.
Focus 2.  {
rewrite Zlength_correct. rewrite firstn_length. rewrite min_l.
rewrite Z2Nat.id by omega; auto.
apply le_trans with (length vp').
rewrite <- (Nat2Z.id (length vp')).
apply Z2Nat.inj_le; try omega. rewrite <- Zlength_correct; omega.
clear - Hvpx He H99.
replace (length vpx) with (length (vp' ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef)).
rewrite app_length; omega.
apply JMeq_length; auto.
apply JMeq_trans with (y:=vpe); auto.
} Unfocus.
Focus 2. {
rewrite Zlength_correct.
rewrite firstn_length. rewrite min_l. rewrite Z2Nat.id by omega. omega.
rewrite skipn_length.
replace (length vpx) with (Z.to_nat (Zlength (vp' ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef))).
rewrite <- Z2Nat.inj_sub by omega.
apply Z2Nat.inj_le; try omega.
rewrite Zlength_app.
rewrite (Zlength_correct (list_repeat _ _)). omega.
rewrite Zlength_app. 
rewrite (Zlength_correct (list_repeat _ _)).
rewrite length_list_repeat.
destruct (zlt (lop+len) (Zlength vp') ).
omega.
rewrite Z2Nat.id; try omega.
rewrite Zlength_correct. rewrite Nat2Z.id.
apply JMeq_length; auto.
apply JMeq_trans with (y:=vpe); auto.
} Unfocus.

normalize.
rewrite sepcon_assoc.
rewrite <- sepcon_comm.
rewrite flatten_sepcon_in_SEP.
rewrite flatten_sepcon_in_SEP.
pose (witness := (shp,
                              field_address0 tp (ArraySubsc lop :: pathp) p,
                              len,  c)).
pose (Frame := 
         `(array_at shp tp pathp (lop + len) np
              (skipn (Z.to_nat lop + Z.to_nat len) vpx) p)
          :: `(array_at shp tp pathp 0 lop (firstn (Z.to_nat lop) vpx) p)
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
 pose (H6 := True).
 pose (H2 := True).
 pose (H1 := True).
 unfold Frame; go_lowerx.
 replace (lop+len-lop)%Z with len by omega.
 super_unfold_lift.
 simpl.
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp.
 Focus 2. {
 unfold temp, make_args'.
 unfold_lift. simpl.
 unfold eval_id. simpl. rewrite <- H10, <- H12.
 rewrite TCp, TCc, TCn.
 simpl.
 split.
 unfold field_address0.
 if_tac; [ |  reflexivity].
 destruct H14 as [? _]; destruct p; try contradiction; reflexivity.
 split.
 rewrite <- H11; reflexivity.
 split; auto.
 } Unfocus.
 cancel.
*
 pose (H10 := True).
 pose (H11 := True).
 pose (H12 := True).
 go_lowerx.
 normalize.
 cancel.
 clear witness Frame.
 hnf in H13. normalize in H13.
 subst x. clear H10 H11 H12 H9 H2 H7 H6  H8 rho.
assert (exists (vpy : list (reptype (nested_field_type2 tp (ArraySubsc 0 :: pathp)))),
                  JMeq vpy vp'').
 rewrite H99. eauto.
destruct H2 as [vpy H8].
rewrite (array_seg_reroot_lemma shp tp pathp tuchar np
              noattr lop (lop+len) (firstn (Z.to_nat lop) vpy)
                  (firstn (Z.to_nat len) (skipn (Z.to_nat lop) vpy))
                  (skipn (Z.to_nat lop + Z.to_nat len) vpy)
                  (list_repeat (Z.to_nat len) (Vint c))
                  ); auto; try omega.
+ replace (lop+len-lop)%Z with len by omega.
    replace (firstn (Z.to_nat lop) vpx) with (firstn (Z.to_nat lop) vpy).
    replace (skipn (Z.to_nat lop + Z.to_nat len) vpx) 
     with (skipn (Z.to_nat lop + Z.to_nat len) vpy).
    cancel.
    rewrite <- Z2Nat.inj_add; try omega.
    clear - H8 H4 He Hvpx H99 Hlop Hvp' Hnp Hlen.
    apply JMeq_eq.
    apply JMeq_trans 
      with (y:= skipn (Z.to_nat (lop + len)) (splice_into_list lop (lop + len) np
          (list_repeat (Z.to_nat len) (Vint c)) vp')).
   apply JMeq_skipn; auto. eapply JMeq_trans; try eassumption.
    apply JMeq_trans 
      with (y:= skipn (Z.to_nat (lop + len)) (vp' ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef)).
   apply eq_JMeq.
   forget (list_repeat (Z.to_nat len) (Vint c)) as bl.
   { clear - Hlop Hlen Hvp' Hnp.
     assert (Z.to_nat lop <= length vp').
       rewrite <- (Nat2Z.id (length vp')), <- Zlength_correct.
       apply Z2Nat.inj_le; omega.
     assert (Z.to_nat len =
                   length (firstn (Z.to_nat len) (bl ++ list_repeat (Z.to_nat len) Vundef))).
       rewrite firstn_length, min_l; auto .
       rewrite app_length, length_list_repeat. omega.
     unfold splice_into_list.
     rewrite firstn_app1 by auto.
     replace (lop+len-lop)%Z with len by omega.
     rewrite Z2Nat.inj_add by omega.
     repeat rewrite <- skipn_skipn.
     rewrite skipn_app1 by (rewrite firstn_length, min_l; omega).
     rewrite (skipn_short (Z.to_nat lop))  by (rewrite firstn_length, min_l; omega).
     simpl app.
     rewrite (skipn_app1 _ (Z.to_nat lop) vp') by auto.
     rewrite skipn_app1 by omega.
     rewrite skipn_short by omega.
     simpl.
     rewrite firstn_same; auto.
     rewrite skipn_length.
     rewrite app_length, length_list_repeat.
     rewrite skipn_length.
     rewrite <- (Nat2Z.id (length vp')), <- Zlength_correct.
     rewrite <- Z2Nat.inj_sub by omega.
     rewrite <- Z2Nat.inj_add by omega.
     rewrite <- Z2Nat.inj_sub by omega.
     apply Z2Nat.inj_le; omega.
   }
   apply JMeq_skipn; auto.
   apply JMeq_trans with (y := vpe); auto.
 assert (0 <= lop <= Zlength vp')%Z by omega.
   apply JMeq_eq.
 apply JMeq_trans with (y:= firstn (Z.to_nat lop)  (splice_into_list lop (lop + len) np
          (list_repeat (Z.to_nat len) (Vint c)) vp')).
 apply JMeq_firstn; auto. eapply JMeq_trans; try eassumption.
 apply JMeq_trans with (y := firstn (Z.to_nat lop) (vp' ++ list_repeat (Z.to_nat (np - Zlength vp')) Vundef)).
  apply eq_JMeq.
 rewrite firstn_splice_into_list; auto.
 rewrite firstn_app1; auto.
 rewrite <- (Nat2Z.id (length vp')). rewrite <- Zlength_correct.
   apply Z2Nat.inj_le; omega.
 apply JMeq_firstn; auto.
 apply JMeq_trans with (y := vpe); auto.  
+  
   apply JMeq_trans with (y:=   firstn (Z.to_nat len) (skipn (Z.to_nat lop) (splice_into_list lop (lop + len) np
          (list_repeat (Z.to_nat len) (Vint c)) vp'))).
  apply JMeq_firstn; auto. apply JMeq_skipn; auto. eapply JMeq_trans; eassumption.
  apply eq_JMeq.
assert (Z.to_nat len <= length (list_repeat (Z.to_nat len) (Vint c))). {
 rewrite length_list_repeat. omega.
}
 unfold splice_into_list.
 rewrite skipn_app2.
 rewrite firstn_length, min_l. rewrite minus_diag. rewrite skipn_0.
 replace (lop+len-lop)%Z with len by omega.
 rewrite firstn_app1.
 rewrite firstn_app1 by auto.
 pattern (Z.to_nat len) at 2;  replace (Z.to_nat len) with (Z.to_nat len + 0) by omega.
 rewrite firstn_firstn.
 auto.
 rewrite firstn_same by (rewrite length_list_repeat; omega). auto.
 rewrite firstn_app1 by (rewrite length_list_repeat; omega).
 rewrite firstn_length, min_l; try omega.
 rewrite app_length.
 rewrite length_list_repeat.
 rewrite <- (Nat2Z.id (length vp')). rewrite <- Zlength_correct.
 destruct (zlt lop (Zlength vp')).
 apply Z2Nat.inj_lt in l; try omega.
  rewrite <- Z2Nat.inj_add; try omega.
 apply Z2Nat.inj_le; try omega.
 rewrite firstn_app1.
 rewrite firstn_length. rewrite min_l; try omega.
 rewrite <- (Nat2Z.id (length vp')). rewrite <- Zlength_correct.
 apply Z2Nat.inj_le; try omega.
 rewrite <- (Nat2Z.id (length vp')). rewrite <- Zlength_correct.
 apply Z2Nat.inj_le; try omega.
+
 rewrite <- skipn_skipn.
 rewrite firstn_skipn. rewrite firstn_skipn. auto.
+
 rewrite Zlength_correct, firstn_length, min_l.
 apply Z2Nat.id. omega.
 transitivity (length   (splice_into_list lop (lop + len) np
                                (list_repeat (Z.to_nat len) (Vint c)) vp')).
 rewrite <- (Nat2Z.id (length _)). rewrite <- Zlength_correct. 
 rewrite length_splice_into_list; try omega.
 apply Z2Nat.inj_le; try omega.
 apply NPeano.Nat.eq_le_incl.
 apply JMeq_length; auto.
 apply JMeq_trans with (y:=vp''); auto.
+
 rewrite Zlength_correct. rewrite firstn_length, min_l. rewrite Z2Nat.id by omega. omega.
 rewrite skipn_length.
 replace (length vpy) with (length (splice_into_list lop (lop + len) np
          (list_repeat (Z.to_nat len) (Vint c)) vp'))
  by (apply JMeq_length; auto; apply JMeq_trans with (y:=vp''); auto).
 rewrite <- (Nat2Z.id (length _)). rewrite <- Zlength_correct. 
 rewrite length_splice_into_list; try omega.
 rewrite <- Z2Nat.inj_sub by omega.
 apply Z2Nat.inj_le; omega.
Qed.
