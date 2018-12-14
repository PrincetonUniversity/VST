Require Import VST.floyd.proofauto.
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
destruct H as [H0 [[H1 H6] [H2 H4]]].
assert (H3 := s256a_data_Zlength_less a).
unfold_data_at (data_at _ _ _ _).

assert_PROP (Zlength r_data = CBLOCKz
    /\ r_data = map Vubyte (s256a_data a) ++ sublist (Zlength (s256a_data a)) CBLOCKz r_data
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
subst r_h r_Nh r_Nl r_num.
forward. (* p = c->data;  *)
simpl (temp _p _).
assert_PROP (field_address t_struct_SHA256state_st [StructField _data] c = offset_val 40 c).
 entailer!.
rewrite <- H0; clear H0.
forward. (* n = c->num; *)
assert (Hddlen: 0 <= Zlength (s256a_data a) < 64) by Omega1.
forward. (* p[n] = 0x80; *)
change (Int.zero_ext 8 (Int.repr 128)) with (Int.repr 128).
rewrite upd_Znth_append
  by (autorewrite with sublist; Omega1).
simpl.
forward. (* n++; *)
eapply semax_seq'.
*
eapply semax_post_flipped'.
match goal with |- context [Sifthenelse _ ?c _] => change c with Body_final_if1 end.
rewrite add_repr.
simple apply final_if1; auto.
intros.
apply andp_left2; apply derives_refl.
*
abbreviate_semax.
Intros hashed' dd' pad.
rename H1 into DDbytes'.
rename H2 into PAD.
unfold_data_at (data_at _ _ _ _).
erewrite (field_at_Tarray wsh _ [StructField _data]); try reflexivity; try apply JMeq_refl; try omega.
2: apply compute_legal_nested_field_spec'; repeat constructor.
rewrite (split2_array_at _ _ _ 0 (Zlength dd') 64); try Omega1.
2: autorewrite with sublist; Omega1.
 rewrite (split2_array_at _ _ _ (Zlength dd') 56 64); try Omega1.
2:autorewrite with sublist; Omega1.
 assert (0 <= Zlength dd' <= 56) by Omega1.
 autorewrite with sublist.
 replace (CBLOCKz - Zlength dd' - (56 - Zlength dd')) with 8 by Omega1.
forward_call (* memset (p+n,0,SHA_CBLOCK-8-n); *)
  (wsh,
     field_address0 t_struct_SHA256state_st
         [ArraySubsc (Zlength dd'); StructField _data] c,
     (Z.of_nat CBLOCK - 8 - Zlength dd')%Z,
     Int.zero).
{apply prop_right; repeat constructor; hnf; simpl; auto.
 rewrite field_address_offset by auto with field_compatible.
 rewrite field_address0_offset by auto with field_compatible.
 make_Vptr c. simpl. unfold Ptrofs.of_intu, Ptrofs.of_int. normalize.
 rewrite !mul_repr, !sub_repr.  (* Why didn't [normalize] do this? *)
 reflexivity.
}
{
change  (Z.of_nat CBLOCK - 8 - Zlength dd')
   with (56 - Zlength dd').
replace (memory_block wsh (56 - Zlength dd'))
 with (memory_block wsh (sizeof (tarray tuchar (56 - Zlength dd'))))
  by (f_equal; rewrite sizeof_tarray_tuchar; auto; omega).
cancel.
}
 split; auto. change (Z.of_nat CBLOCK) with CBLOCKz. Omega1.

forward.  (* p += SHA_CBLOCK-8; *)
assert_PROP (force_val
         (sem_add_ptr_int tuchar Signed
            (field_address t_struct_SHA256state_st [StructField _data] c)
            (Vint (Int.sub (Int.mul (Int.repr 16) (Int.repr 4))
                        (Int.repr 8))))
       = field_address t_struct_SHA256state_st
                [ArraySubsc (CBLOCKz - 8); StructField _data] c). {
  entailer!.
  make_Vptr c.
  rewrite !field_address_offset by auto with field_compatible.
  simpl. normalize.
 }
 simpl (temp _p _).
 rewrite H2. clear H2.
 eapply semax_pre_post; [ | | | | |
  apply final_part2 with (wsh:=wsh)(shmd:=shmd)(hashed:= s256a_hashed a)(pad:=pad)(c:=c)(gv:=gv)(md:=md);
  try eassumption; try Omega1; try apply s256a_hashed_divides].
+
change (Z.of_nat CBLOCK) with CBLOCKz.
change (Z.to_nat 8) with (Z.to_nat (CBLOCKz-56)).
entailer!.
erewrite field_at_Tarray; try reflexivity; try apply JMeq_refl; try omega;
  [ | compute; clear; intuition].
rewrite (split3seg_array_at _ _ _ 0 (Zlength dd') 56 64); try Omega1.
2: rewrite !Zlength_app, !Zlength_map, !Zlength_list_repeat by omega;
  omega.
autorewrite with sublist in *|-.
simpl.
autorewrite with sublist.
cancel.
rewrite array_at_data_at'; auto; try apply derives_refl; omega.
+
subst POSTCONDITION; unfold abbreviate; simpl_ret_assert; normalize.
+
subst POSTCONDITION; unfold abbreviate; simpl_ret_assert; normalize.
+
subst POSTCONDITION; unfold abbreviate; simpl_ret_assert; normalize.
+
intros.
subst POSTCONDITION; unfold abbreviate; simpl_ret_assert.
rewrite hashed_data_recombine by auto.
apply ENTAIL_refl.
+
symmetry; rewrite <- hashed_data_recombine at 1; auto.
unfold s256a_len.
autorewrite with sublist.
auto.
Time Qed.  (* 40.5 sec (14.375u) *)

