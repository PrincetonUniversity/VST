Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.verif_sha_final2.
Require Import sha.verif_sha_final3.
Local Open Scope logic.


Lemma upd_Znth_append:
 forall (t: Type) len N dd ee (v: t), 
   len = Zlength dd ->
   len < N ->
   N <= Zlength ee ->
   upd_Znth len (dd++ sublist len N ee) v =
    (dd ++ [v]) ++ sublist (len+1) N ee.
Proof.
intros. subst.
unfold upd_Znth.
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
  nested_field_type t1 gfs = tarray t n ->
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
assert (exists v1': list (reptype (nested_field_type t1 (gfs SUB 0))), JMeq v1 v1').
clear - H.
rewrite nested_field_type_ind.
revert v1 H. 
forget (nested_field_type t1 gfs) as tx.
intros. subst. simpl.
revert v1. rewrite reptype_eq.  simpl. 
intros; eauto. 
destruct H1 as [v1' H1].
assert (exists v2': list (reptype (nested_field_type t1 (gfs SUB 0))), JMeq v2 v2').
clear - H.
rewrite nested_field_type_ind.
revert v2 H. 
forget (nested_field_type t1 gfs) as tx.
intros. subst. simpl.
revert v2. rewrite reptype_eq.  simpl. 
intros; eauto. 
destruct H2 as [v2' H2].
  pose proof (Zlength_nonneg al); 
  pose proof (Zlength_nonneg bl).
rewrite (field_at_Tarray sh t1 gfs t (Zlength (al++bl)) noattr v1 v1')
  by (auto; apply Zlength_nonneg).
rewrite (field_at_Tarray sh t1 gfs t (Zlength (al++bl)) noattr v2 v2')
  by (auto; apply Zlength_nonneg).
rewrite (add_andp _ _ (array_at_local_facts _ _ _ _ _ _ _)).
normalize.
rewrite (split2_array_at _ _ _ 0 (Zlength al) (Zlength (al++bl)))
  by (try omega; rewrite Zlength_app; omega).
rewrite (split2_array_at _ _ _ 0 (Zlength al) (Zlength (al++bl))).
2: rewrite Zlength_app; omega.
Focus 2. {
  apply (JMeq_trans (JMeq_sym H4)) in H2.
  erewrite <- list_func_JMeq with (f := Zlength); [| | exact H2].
  2: rewrite nested_field_type_ind; rewrite H; auto.
  rewrite !Zlength_app, Zlength_list_repeat by omega.
  omega.
} Unfocus.
apply (JMeq_trans (JMeq_sym H3)) in H1.
apply (JMeq_trans (JMeq_sym H4)) in H2.
apply sepcon_derives.
apply derives_refl'.
f_equal.
rewrite Z.sub_0_r.
clear - H1 H2 H5 H.
revert v1' v2' H1 H2.
rewrite nested_field_type_ind.
rewrite H.
simpl.
intros.
apply JMeq_eq in H1; apply JMeq_eq in H2.
rewrite <- H1. rewrite <- H2.
autorewrite with sublist. auto.
eapply derives_trans; [apply array_at_array_at_ | ].
unfold array_at_.
apply derives_refl'.
f_equal.
rewrite Z.sub_0_r.
clear - H2 H5 H.
revert v2' H2.
rewrite nested_field_type_ind.
rewrite H.
simpl.
intros. apply JMeq_eq in H2; rewrite <- H2.
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
assert (CB := CBLOCKz_eq).
unfold sha256state_.
Intros r. destruct r as [r_h [r_Nl [r_Nh [r_data r_num]]]].
unfold s256_relate in H.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd in H.
destruct H as [H0 [[H1 H6] [H2 [DDbytes H4]]]].
assert (H3 := s256a_data_Zlength_less a).
unfold_data_at 1%nat.

assert_PROP (Zlength r_data = CBLOCKz
    /\ r_data = map Vint (map Int.repr (s256a_data a)) ++ sublist (Zlength (s256a_data a)) CBLOCKz r_data
    /\ field_compatible t_struct_SHA256state_st [StructField _data] c)
   as H; [ | destruct H as [H [H7 FC]]].
  { entailer!.
    simplify_value_fits in H12; destruct H12 as [LEN _].
     split; auto.
    change  (@reptype CompSpecs tuchar) with val in LEN. (* should not be necessary *) 
    rewrite <- H2.
    pose proof (Zlength_nonneg (s256a_data a)).
    rewrite <- sublist_split; autorewrite with sublist; try omega.
    auto.
   }
rewrite H7. clear H7.
subst r_Nh r_Nl r_num.
assert (H3': Zlength (s256a_data a) < 64) by assumption.
forward. (* p = c->data;  *)
 assert_LOCAL (temp _p (field_address t_struct_SHA256state_st [StructField _data] c))
    by entailer!. 
 drop_LOCAL 1%nat.
forward. (* n = c->num; *)
rewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
assert (Hddlen: 0 <= Zlength (s256a_data a) < 64) by Omega1.
forward. (* p[n] = 0x80; *)
change (Int.zero_ext 8 (Int.repr 128)) with (Int.repr 128).
rewrite upd_Znth_append
  by (autorewrite with sublist; Omega1).
simpl.
forward. (* n++; *)
forward_if   (invariant_after_if1 (s256a_hashed a) (s256a_data a) c md shmd kv).
* (* then-clause *)
 change Delta with Delta_final_if1.
 match goal with |- semax _ _ ?c _ => change c with Body_final_if1 end.
 make_sequential.
 unfold POSTCONDITION, abbreviate.
 normalize_postcondition.
(*  subst ddlen.*)
 assert (Zlength (s256a_data a) + 1 > 16 * 4 - 8) by omega.
 assert (DDbytes': Forall isbyteZ (s256a_data a)).
 unfold s256a_data. apply Forall_sublist; auto.
 eapply semax_pre; 
  [|apply (ifbody_final_if1 Espec (s256a_hashed a) md c shmd (s256a_data a) kv (s256a_hashed_divides _) H3' H4 DDbytes')].
 entailer!.
 unfold_data_at 1%nat.
 rewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
 simpl.
 change (cons (Vint (Int.repr 128))) with (app [Vint (Int.repr 128)]).
 rewrite <- !(app_ass _ [_]).
 rewrite <- app_nil_end.
 unfold s256a_regs.
 rewrite bitlength_eq.
 rewrite S256abs_recombine by auto.
 cancel.
 unfold data_at.
 eapply cancel_field_at_array_partial_undef; try reflexivity; try apply JMeq_refl.
 autorewrite with sublist; Omega1.
 apply eq_JMeq. f_equal. f_equal. f_equal.
 autorewrite with sublist; Omega1. 
* (* else-clause *)
forward. (* skip; *)
unfold invariant_after_if1.
Exists (s256a_hashed a) ((s256a_data a) ++ [128]) 0.
entailer!.
split3.
rewrite Forall_app; split; auto.
unfold s256a_data; apply Forall_sublist; auto.
repeat constructor; omega.
split.
rewrite app_length; simpl. apply Nat2Z.inj_ge.
repeat rewrite Nat2Z.inj_add. 
change (Z.of_nat CBLOCK) with 64.
rewrite <- Zlength_correct. 
change (Z.of_nat 1) with 1%Z; change (Z.of_nat 8) with 8%Z.
omega.
apply s256a_hashed_divides.
f_equal. repeat rewrite Zlength_correct; f_equal.
rewrite app_length; simpl. rewrite Nat2Z.inj_add; reflexivity.
unfold_data_at 1%nat.
unfold s256a_regs.
rewrite bitlength_eq.
 rewrite S256abs_recombine by auto.
cancel.
rewrite (field_at_data_at _ _ [_]).
eapply cancel_field_at_array_partial_undef; try reflexivity; try apply JMeq_refl.
autorewrite with sublist; Omega1.
apply eq_JMeq. simpl. f_equal.
rewrite !map_app. reflexivity.
f_equal. f_equal. autorewrite with sublist; Omega1. 
* unfold invariant_after_if1.
Intros hashed' dd' pad.
rename H1 into DDbytes'.
rename H2 into PAD.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
unfold SHA_256.
unfold_data_at 1%nat.
erewrite (field_at_Tarray Tsh _ [StructField _data]); try reflexivity; try apply JMeq_refl; try omega.
rewrite (split2_array_at _ _ _ 0 (Zlength dd') 64); try Omega1.
3: apply compute_legal_nested_field_spec'; repeat constructor.
Focus 2. {
  rewrite Zlength_app, !Zlength_map, Zlength_list_repeat; try omega.
  + assert (length dd' <= 56)%nat by (change CBLOCK with 64%nat in H5; omega).
    rewrite Zlength_correct. omega.
} Unfocus.
 rewrite (split2_array_at _ _ _ (Zlength dd') 56 64); try Omega1.
Focus 2. {
  rewrite !Zlength_app, !Zlength_map, !Zlength_list_repeat, Zlength_sublist; try omega.
  + assert (length dd' <= 56)%nat by (change CBLOCK with 64%nat in H5; omega).
    rewrite !Zlength_correct. omega.
  + rewrite !Zlength_app, !Zlength_map, !Zlength_list_repeat; try omega.
    assert (length dd' <= 56)%nat by (change CBLOCK with 64%nat in H5; omega).
    rewrite Zlength_correct. omega.
  + assert (length dd' <= 56)%nat by (change CBLOCK with 64%nat in H5; omega).
    rewrite Zlength_correct. omega.
} Unfocus.
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
     Int.zero).
{apply prop_right; repeat constructor; hnf; simpl; auto.
 rewrite field_address_offset by auto with field_compatible.
 rewrite field_address0_offset by auto with field_compatible.
 make_Vptr c. simpl. normalize. 
}
{
change  (Z.of_nat CBLOCK - 8 - Zlength dd')
   with (56 - Zlength dd').
entailer!.
replace (memory_block Tsh (56 - Zlength dd'))
 with (memory_block Tsh (sizeof (tarray tuchar (56 - Zlength dd'))))
  by (f_equal; rewrite sizeof_tarray_tuchar; auto; omega).
cancel.
}
 split; auto.  Omega1.

normalize.
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
make_Vptr c.
 rewrite !field_address_offset by auto with field_compatible.
simpl. normalize.
eapply semax_pre_post; [ | | 
  apply final_part2 with (hashed:= s256a_hashed a)(pad:=pad)(c:=c)(kv:=kv)(md:=md); 
  try eassumption; try Omega1; try apply s256a_hashed_divides].
+
change (Z.of_nat CBLOCK) with CBLOCKz.
change (Z.to_nat 8) with (Z.to_nat (CBLOCKz-56)).
entailer!.
erewrite field_at_Tarray; try reflexivity; try apply JMeq_refl; try omega.
2: compute; clear; intuition.
rewrite (split3seg_array_at _ _ _ 0 (Zlength dd') 56 64); try Omega1.
Focus 2. {
  rewrite !Zlength_app, !Zlength_map, !Zlength_list_repeat by omega.
  omega.
} Unfocus.
progress (autorewrite with sublist).
cancel.
rewrite array_at_data_at_rec; auto; omega.
+
intros.
autorewrite with ret_assert.
rewrite hashed_data_recombine by auto.
apply andp_left2; auto.
+
reflexivity.
+
unfold s256a_data.
apply Forall_sublist; auto.
Time Qed.

