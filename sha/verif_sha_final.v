Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.verif_sha_final2.
Require Import sha.verif_sha_final3.
Local Open Scope logic.


Lemma upd_reptype_array_append:
 forall t len dd v, 
   len = Zlength dd ->
   upd_reptype_array t len dd v =
    dd ++ [v].
Proof.
intros. subst.
unfold upd_reptype_array.
normalize.
rewrite force_lengthn_id by auto.
rewrite skipn_short; auto.
change nat_of_Z with Z.to_nat.
rewrite Z2Nat.inj_add; try omega.
rewrite Zlength_correct. rewrite Nat2Z.id.
omega.
apply Zlength_nonneg.
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
unfold_data_at 1%nat.
normalize.
unfold s256_relate in H0.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd in H0|-*.
destruct a as [hashed dd].
destruct H0 as [H0 [[H1 H6] [H2 [[H3 DDbytes] [H4 H5]]]]].
subst r_Nh r_Nl r_num r_data.
assert (H3': (Zlength dd < 64)%Z) by assumption.
forward. (* p = c->data;  *)
(* This proof should be a lot nicer. *)
 assert_LOCAL (temp _p (field_address t_struct_SHA256state_st [StructField _data] c)).
 { entailer. 
   rewrite field_at_compatible'.
   entailer!.
   unfold field_address; rewrite if_true by auto. reflexivity.
 }
 drop_LOCAL 1%nat.
forward. (* n = c->num; *)
rewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
normalize.
forward. (* p[n] = 0x80; *)
{
  change (nested_field_type2
    (nested_field_type2 t_struct_SHA256state_st [StructField _data]) []) with (tarray tuchar 64).
  entailer!.
  rewrite Zlength_correct in H3' |- *.
  omega.
}
change (Int.zero_ext 8 (Int.repr 128)) with (Int.repr 128).
replace (data_at Tsh
           (nested_field_type2 t_struct_SHA256state_st [StructField _data])
           (upd_reptype_array tuchar (Zlength dd)
              (map Vint (map Int.repr dd)) (Vint (Int.repr 128)))) with
  (data_at Tsh
           (nested_field_type2 t_struct_SHA256state_st [StructField _data])
              (map Vint (map Int.repr (dd ++ [128])))).
Focus 2.
{
  rewrite !map_app.
  simpl (map Vint (map Int.repr [128])).
  apply eq_sym.
  apply equal_data_one_more_on_list.
  + reflexivity.
  + omega.
  + rewrite !Zlength_map. reflexivity.
} Unfocus.

forward n_old. (* n++; *)
simpl. normalize. 
subst r_h. simpl.
set (ddlen :=  Zlength dd).
assert (Hddlen: (0 <= ddlen < 64)%Z).
unfold ddlen. split; auto. rewrite Zlength_correct; omega.
repeat rewrite  initial_world.Zlength_map.
forward_if   (invariant_after_if1 hashed dd c md shmd kv).
* (* then-clause *)
 change Delta with Delta_final_if1.
match goal with |- semax _ _ ?c _ => change c with Body_final_if1 end.
  make_sequential.
  normalize_postcondition.
unfold ddlen in *; clear ddlen.
assert (Zlength dd + 1 > 16 * 4 - 8) by omega.
eapply semax_pre0; 
  [|apply (ifbody_final_if1 Espec hashed md c shmd dd kv H4 H3 H2 DDbytes)].
entailer!.
unfold_data_at 2%nat.
rewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
rewrite upd_reptype_array_append
  by (rewrite !Zlength_map; auto).
entailer!.
* (* else-clause *)
forward. (* skip; *)
unfold invariant_after_if1.
apply exp_right with hashed.
apply exp_right with (dd ++ [128]).
apply exp_right with 0%Z.
entailer.
apply andp_right; [apply prop_right; repeat split | cancel].
rewrite Forall_app; split; auto.
repeat constructor; omega.
rewrite app_length; simpl. apply Nat2Z.inj_ge.
change (Z.of_nat CBLOCK) with 64; unfold ddlen in H0; 
  rewrite Zlength_correct in H0.
repeat rewrite Nat2Z.inj_add. 
change (Z.of_nat 1) with 1%Z; change (Z.of_nat 8) with 8%Z.
omega.
f_equal. unfold ddlen; repeat rewrite Zlength_correct; f_equal.
rewrite app_length; simpl. rewrite Nat2Z.inj_add; reflexivity.
unfold_data_at 2%nat.
rewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
rewrite !map_app.
rewrite upd_reptype_array_append
  by (rewrite !Zlength_map; auto).
entailer!.
* unfold invariant_after_if1.
forward_intro hashed'.
forward_intro dd'.
forward_intro pad.
apply semax_extract_PROP; intro DDbytes'.
apply semax_extract_PROP; intro PAD.
normalize.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
unfold sha_finish.
unfold SHA_256.

    unfold_data_at 1%nat.
    replace (field_at Tsh t_struct_SHA256state_st [StructField _data]
        (map Vint (map Int.repr dd')) c) with
      (field_at Tsh t_struct_SHA256state_st [StructField _data]
        (map Vint (map Int.repr dd') ++ 
         list_repeat (CBLOCK - 8 - length dd')%nat Vundef ++ []) c).
    Focus 2. {
      erewrite field_at_data_equal; [reflexivity |].
      rewrite app_nil_r.
      apply data_equal_sym, data_equal_list_repeat_default.
    } Unfocus.
    erewrite array_seg_reroot_lemma
      with (gfs := [StructField _data]) (lo := Zlength dd') (hi := Z.of_nat CBLOCK - 8);
      [| | | reflexivity | | reflexivity | reflexivity | | ].
    2: rewrite Zlength_correct; omega.
    Focus 2. {
      apply Nat2Z.inj_le in H0.
      rewrite Nat2Z.inj_add in H0.
      rewrite Zlength_correct.
      change 8 with (Z.of_nat 8).
    omega.
    } Unfocus.
    2: change (Z.of_nat CBLOCK) with 64; omega.
    2: rewrite !Zlength_map; reflexivity.
    Focus 2. {
      rewrite !Zlength_correct.
      rewrite length_list_repeat.
      rewrite !Nat2Z.inj_sub by omega.
      reflexivity.
    } Unfocus.
    normalize.

forward_call' (* memset (p+n,0,SHA_CBLOCK-8-n); *)
  (Tsh,
     field_address0 t_struct_SHA256state_st
         [ArraySubsc (Zlength dd'); StructField _data] c, 
     (Z.of_nat CBLOCK - 8 - Zlength dd')%Z,
     Int.zero) vret.
 apply prop_right; repeat constructor; hnf; simpl; auto.
 rewrite field_address_clarify by auto.
 rewrite field_address0_clarify by auto.
 erewrite nested_field_offset2_Tarray by reflexivity.
  change (sizeof tuchar) with 1.
 rewrite Z.mul_1_l.
 normalize.
 {pull_left (data_at Tsh (Tarray tuchar (Z.of_nat CBLOCK - 8 - Zlength dd') noattr)
     (list_repeat (CBLOCK - 8 - length dd') Vundef)
     (field_address0 t_struct_SHA256state_st
              [ArraySubsc (Zlength dd'); StructField _data] c)).
    repeat rewrite sepcon_assoc; apply sepcon_derives; [ | cancel].
    eapply derives_trans; [apply data_at_data_at_; reflexivity |].
    assert (sizeof (Tarray tuchar (Z.of_nat CBLOCK - 8 - Zlength dd') noattr) =
              Z.of_nat CBLOCK - 8 - Zlength dd').
    Focus 1. {
Opaque tuchar.
      simpl.
Transparent tuchar.
      change (sizeof tuchar) with 1.
      rewrite Z.mul_1_l.
      rewrite Z.max_r; [reflexivity |].
      apply Nat2Z.inj_le in H0.
      rewrite Nat2Z.inj_add in H0.
      rewrite Zlength_correct.
      change 8 with (Z.of_nat 8).
      omega.
    } Unfocus.
    rewrite data_at__memory_block; [| reflexivity |].
    Focus 2. {
       change Int.modulus with 4294967296.
       assert (Z.of_nat CBLOCK = 64) by reflexivity.
       pose proof Zlength_correct dd'.
       omega.
    } Unfocus.
    rewrite H7.
    entailer!.
 }
 split; auto.
 Omega1.
 
normalize.
clear vret H7.
forward p_old.  (* p += SHA_CBLOCK-8; *)

gather_SEP 0 1 2.
replace_SEP 0 (`(field_at Tsh t_struct_SHA256state_st [StructField _data]
  (map Vint (map Int.repr dd') ++ (list_repeat (Z.to_nat (Z.of_nat CBLOCK - 8 - Zlength dd'))
   (Vint Int.zero)) ++ []) c)).
  {
    erewrite array_seg_reroot_lemma
      with (gfs := [StructField _data]) (lo := Zlength dd') (hi := Z.of_nat CBLOCK - 8);
      [| | | reflexivity | | reflexivity | reflexivity | | ].
    2: rewrite Zlength_correct; omega.
    Focus 2. {
      apply Nat2Z.inj_le in H0.
      rewrite Nat2Z.inj_add in H0.
      rewrite Zlength_correct.
      change 8 with (Z.of_nat 8).
    omega.
    } Unfocus.
    2: change (Z.of_nat CBLOCK) with 64; omega.
    2: rewrite !Zlength_map; reflexivity.
    Focus 2. {
      rewrite !Zlength_correct.
      rewrite length_list_repeat.
      rewrite !Z2Nat.id by omega.
      reflexivity.
    } Unfocus.
    entailer!.
  }
  match goal with
  | |- semax _ (PROPx nil (LOCALx (_ :: ?L) (SEPx ?S))) _ _ =>
         eapply semax_pre with (PROPx nil (LOCALx
          ((temp _p (field_address t_struct_SHA256state_st
            [ArraySubsc (Z.of_nat CBLOCK - 8); StructField _data] c))
            :: L) (SEPx S)))
  end.
  Focus 1. {
    clear POSTCONDITION.
    entailer!.
    clear rho H9 H8.
    (* this proof should be nicer. *)
    rewrite field_address_clarify.
    rewrite field_address_clarify.
    normalize.
    unfold field_address in *.
    if_tac in TC0; try contradiction.
    destruct c_; try contradiction; apply I.
    unfold field_address in *.
    if_tac in TC0; try contradiction.
    rewrite if_true.
    destruct c_; try contradiction. apply I.
    eapply field_compatible_cons_Tarray; try reflexivity; auto.
  } Unfocus.
  subst n_old p_old.
  replace Delta with Delta_final_if1 by (simplify_Delta; reflexivity).
  eapply semax_pre; [ | apply final_part2 with pad; try eassumption; try reflexivity].
  entailer!.
Qed.
