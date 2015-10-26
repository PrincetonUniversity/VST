Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.verif_sha_final2.
Require Import sha.verif_sha_final3.
Local Open Scope logic.


Lemma upd_Znth_in_list_append:
 forall (t: Type) len N dd ee (v: t), 
   len = Zlength dd ->
   len < N ->
   N <= Zlength ee ->
   upd_Znth_in_list len (dd++ sublist len N ee) v =
    (dd ++ [v]) ++ sublist (len+1) N ee.
Proof.
intros. subst.
unfold upd_Znth_in_list.
pose proof (Zlength_nonneg dd).
autorewrite with sublist.
rewrite app_ass.
f_equal.
simpl.
f_equal.
f_equal.
omega.
Qed.

Lemma cancel_field_at_array_partial_undef:
 forall {cs: compspecs} sh t t1 n gfs p (al bl: list (reptype t)) blen v1 v2,
  nested_field_type2 t1 gfs = tarray t n ->
  legal_nested_field t1 gfs ->
  Zlength (al++bl) = n ->
  Zlength bl = blen ->
  JMeq v1 (al++bl) ->
  JMeq v2 (al++list_repeat (Z.to_nat blen) (default_val t)) ->
  field_at sh t1 gfs v1 p
   |-- field_at sh t1 gfs v2 p.
Proof.
intros.
subst.
assert (exists v1': list (reptype (nested_field_type2 t1 (gfs SUB 0))), JMeq v1 v1').
clear - H.
rewrite nested_field_type2_ind.
revert v1 H. 
forget (nested_field_type2 t1 gfs) as tx.
intros. subst. simpl.
revert v1. rewrite reptype_ind.  simpl. 
unfold reptype_array.  intros; eauto. 
destruct H1 as [v1' H1].
assert (exists v2': list (reptype (nested_field_type2 t1 (gfs SUB 0))), JMeq v2 v2').
clear - H.
rewrite nested_field_type2_ind.
revert v2 H. 
forget (nested_field_type2 t1 gfs) as tx.
intros. subst. simpl.
revert v2. rewrite reptype_ind.  simpl. 
unfold reptype_array.  intros; eauto. 
destruct H2 as [v2' H2].
  pose proof (Zlength_nonneg al); 
  pose proof (Zlength_nonneg bl).
rewrite (field_at_Tarray sh t1 gfs t (Zlength (al++bl)) noattr v1 v1')
  by (auto; apply Zlength_nonneg).
rewrite (field_at_Tarray sh t1 gfs t (Zlength (al++bl)) noattr v2 v2')
  by (auto; apply Zlength_nonneg).
rewrite (split2_array_at _ _ _ 0 (Zlength al) (Zlength (al++bl)))
  by (autorewrite with sublist; omega).
rewrite (split2_array_at _ _ _ 0 (Zlength al) (Zlength (al++bl)))
  by (autorewrite with sublist; omega).
rewrite H3 in H1.
rewrite H4 in H2.
clear H3 H4.
apply sepcon_derives.
apply derives_refl'.
f_equal.
rewrite Z.sub_0_r.
clear - H1 H2 H5 H.
revert v1' v2' H1 H2.
rewrite nested_field_type2_ind.
rewrite H.
simpl.
intros.
rewrite <- H1. rewrite <- H2.
autorewrite with sublist. auto.
eapply derives_trans; [apply array_at_array_at_ | ].
unfold array_at_.
apply derives_refl'.
f_equal.
rewrite Z.sub_0_r.
clear - H2 H5 H.
revert v2' H2.
rewrite nested_field_type2_ind.
rewrite H.
simpl.
intros. rewrite <- H2.
rewrite sublist_app2 by omega.
rewrite Z.sub_diag.
autorewrite with sublist.
auto.
Qed.

Lemma body_SHA256_Final: semax_body Vprog Gtot f_SHA256_Final SHA256_Final_spec.
Proof.
start_function.
name md_ _md.
name c_ _c.
name p _p.
name n _n.
name cNl _cNl.
name cNh _cNh.
unfold sha256state_.
forward_intro [r_h [r_Nl [r_Nh [r_data r_num]]]].
unfold data_at. unfold_field_at 1%nat.
pose proof I.
normalize.
unfold s256_relate in H0.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd in H0|-*.
destruct a as [hashed dd].
destruct H0 as [H0 [[H1 H6] [H2 [[H3 DDbytes] [H4 H5]]]]].
clear H.
assert_PROP (Zlength r_data = CBLOCKz
    /\ r_data = map Vint (map Int.repr dd) ++ sublist (Zlength dd) CBLOCKz r_data
    /\ field_compatible t_struct_SHA256state_st [StructField _data] c).
  { entailer!.
    simplify_value_fits in H15; destruct H15 as [H15 _].
     split; auto.
    change  (@reptype CompSpecs tuchar) with val in H15. (* should not be necessary *) 
    rewrite <- H2.
    pose proof CBLOCKz_eq. 
    pose proof (Zlength_nonneg dd).
    rewrite <- sublist_split; autorewrite with sublist; try omega.
    auto.
   }
destruct H as [H [H7 FC]].
rewrite H7. clear H7.
subst r_Nh r_Nl r_num.
assert (H3': Zlength dd < 64) by assumption.
forward. (* p = c->data;  *)
 assert_LOCAL (temp _p (field_address t_struct_SHA256state_st [StructField _data] c))
    by entailer!. 
 drop_LOCAL 1%nat.
forward. (* n = c->num; *)
rewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
normalize.
  change (nested_field_type2 t_struct_SHA256state_st [StructField _data])
   with (tarray tuchar CBLOCKz).
forward. (* p[n] = 0x80; *)
{
   entailer!.
  rewrite Zlength_correct in H3' |- *.
  Omega1.
}
change (Int.zero_ext 8 (Int.repr 128)) with (Int.repr 128).
match goal with |- appcontext [upd_Znth_in_list ?A] =>
   change A with (Zlength dd)
end. (* should not be necessary *)
rewrite upd_Znth_in_list_append
  by (autorewrite with sublist; Omega1).

forward. (* n++; *)
simpl.
set (ddlen :=  Zlength dd).
assert (Hddlen: (0 <= ddlen < 64)%Z).
unfold ddlen. split; auto. rewrite Zlength_correct; omega.
repeat rewrite  initial_world.Zlength_map.
forward_if   (invariant_after_if1 hashed dd c md shmd kv).
* (* then-clause *)
 change Delta with Delta_final_if1.
match goal with |- semax _ _ ?c _ => change c with Body_final_if1 end.
  make_sequential.
  unfold POSTCONDITION, abbreviate.
  normalize_postcondition.
unfold ddlen in *; clear ddlen.
assert (Zlength dd + 1 > 16 * 4 - 8) by omega.
eapply semax_pre0; 
  [|apply (ifbody_final_if1 Espec hashed md c shmd dd kv H4 H3 H5 DDbytes)].
entailer!.
unfold data_at. unfold_field_at 6%nat.
rewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
entailer!.
change (cons (Vint (Int.repr 128))) with (app [Vint (Int.repr 128)]).
rewrite <- !(app_ass _ [_]).
rewrite <- app_nil_end.
unfold data_at.
eapply cancel_field_at_array_partial_undef; try reflexivity.
autorewrite with sublist; Omega1.
apply eq_JMeq. f_equal. f_equal. f_equal.
autorewrite with sublist; Omega1. 
* (* else-clause *)
forward. (* skip; *)
unfold invariant_after_if1.
Exists hashed (dd ++ [128]) 0.
entailer!.
split3.
rewrite Forall_app; split; auto.
repeat constructor; omega.
rewrite app_length; simpl. apply Nat2Z.inj_ge.
repeat rewrite Nat2Z.inj_add. 
change (Z.of_nat CBLOCK) with 64; subst ddlen.
rewrite <- Zlength_correct. 
change (Z.of_nat 1) with 1%Z; change (Z.of_nat 8) with 8%Z.
omega.
f_equal. unfold ddlen; repeat rewrite Zlength_correct; f_equal.
rewrite app_length; simpl. rewrite Nat2Z.inj_add; reflexivity.
unfold data_at. unfold_field_at 6%nat.
repeat rewrite sepcon_assoc.
simple apply sepcon_derives; [now auto | ].
simple apply sepcon_derives; [now auto | ].
simple apply sepcon_derives; [now auto | ].
cancel.
rewrite (field_at_data_at _ _ [_]).
eapply cancel_field_at_array_partial_undef; try reflexivity.
subst ddlen. autorewrite with sublist; Omega1.
apply eq_JMeq. f_equal. 
rewrite !map_app. reflexivity.
f_equal. f_equal. subst ddlen; autorewrite with sublist; Omega1. 
* unfold invariant_after_if1.
Intros hashed' dd' pad.
apply semax_extract_PROP; intro DDbytes'.
apply semax_extract_PROP; intro PAD.
normalize.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
unfold sha_finish.
unfold SHA_256.
unfold data_at. unfold_field_at 1%nat.
erewrite (field_at_Tarray Tsh _ [StructField _data]); try reflexivity; try omega.
rewrite (split2_array_at _ _ _ 0 (Zlength dd') 64); try Omega1.
2: apply compute_legal_nested_field_spec'; repeat constructor.
 rewrite (split2_array_at _ _ _ (Zlength dd') 56 64); try Omega1.
 pose proof CBLOCKz_eq.
 assert (0 <= Zlength dd' <= 56).
    split. apply Zlength_nonneg. rewrite Zlength_correct.
  change (56) with (Z.of_nat (CBLOCK-8)). 
  apply -> Nat2Z.inj_le. omega.
 autorewrite with sublist.
 replace (CBLOCKz - Zlength dd' - (56 - Zlength dd')) with 8 by Omega1.
forward_call (* memset (p+n,0,SHA_CBLOCK-8-n); *)
  (Tsh,
     field_address0 t_struct_SHA256state_st
         [ArraySubsc (Zlength dd'); StructField _data] c, 
     (Z.of_nat CBLOCK - 8 - Zlength dd')%Z,
     Int.zero) vret. 
{apply prop_right; repeat constructor; hnf; simpl; auto.
 unfold field_address, field_address0. rewrite !if_true; try auto.
 make_Vptr c_. simpl. f_equal.  f_equal. 
  rewrite Z.mul_1_l. normalize.
 eapply field_compatible0_cons_Tarray; try reflexivity; eauto; Omega1.
 normalize.
}
{
change  (Z.of_nat CBLOCK - 8 - Zlength dd')
   with (56 - Zlength dd').
entailer!.
replace (memory_block Tsh (56 - Zlength dd'))
 with (memory_block Tsh (sizeof cenv_cs (tarray tuchar (56 - Zlength dd'))))
  by (f_equal; rewrite sizeof_tarray_tuchar; auto; omega).
cancel.
}
 split; auto.  Omega1.
 
normalize.
clear vret H10.
forward.  (* p += SHA_CBLOCK-8; *)
change Delta with Delta_final_if1.
subst POSTCONDITION; unfold abbreviate.
assert_PROP (force_val
         (sem_add_pi tuchar
            (field_address t_struct_SHA256state_st [StructField _data] c)
            (Vint (Int.repr 56))) 
       = field_address t_struct_SHA256state_st
                [ArraySubsc (CBLOCKz - 8); StructField _data] c).
entailer!.
make_Vptr c_.
unfold field_address.
rewrite !if_true.
simpl. normalize.
eapply field_compatible_cons_Tarray; try reflexivity; auto.
auto.
eapply semax_pre_post; [ | | 
  apply final_part2 with (hashed:=hashed)(pad:=pad)(c:=c)(kv:=kv)(md:=md); 
  try eassumption; try Omega1; reflexivity].
+
apply andp_left2.
entailer!.
rewrite <- H11.
unfold field_address.
rewrite !if_true; auto.
normalize.
eapply field_compatible_cons_Tarray; try reflexivity; auto.
erewrite field_at_Tarray; try reflexivity; try omega.
2: compute; clear; intuition.
rewrite (split2_array_at _ _ _ 0 (Zlength dd') 64) by Omega1.
autorewrite with sublist.
rewrite (split2_array_at _ _ _ (Zlength dd') 56 64) by Omega1.
autorewrite with sublist.
cancel.
rewrite array_at_data_at'; auto.
+
intros.
apply andp_left2.
autorewrite with ret_assert.
auto.
Qed.

