Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.verif_sha_final2.
(*Require Import sha.verif_sha_final3.*)
Local Open Scope logic.

Lemma body_SHA256_Final: semax_body Vprog Gtot f_SHA256_Final SHA256_Final_spec.
Proof.
start_function.
name md_ _md.
name c_ _c.
name p _p.
name n _n.
name cNl _cNl.
name cNh _cNh.
unfold sha256state_; normalize.
intros [r_h [r_Nl [r_Nh [r_data r_num]]]].
unfold_data_at 1%nat.
normalize.
unfold s256_relate in H0.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd in H0|-*.
destruct a as [hashed data].
destruct H0 as [H0 [H1 [H2 [[H3 DDbytes] [H4 H5]]]]].
destruct H1 as [hi [lo [? [? ?]]]].
subst r_Nh r_Nl r_num r_data. rename data into dd.
assert (H3': (Zlength dd < 64)%Z) by assumption.
forward. (* p = c->data;  *)
forward. (* n = c->num; *)
rewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
rewrite at_offset'_eq by (rewrite <- data_at_offset_zero; reflexivity).
normalize.
change 40 with (nested_field_offset2 t_struct_SHA256state_st [StructField _data]).
forward. (* p[n] = 0x80; *)
{
  change (nested_field_type2
    (nested_field_type2 t_struct_SHA256state_st [StructField _data]) []) with (tarray tuchar 64).
  entailer!.
  rewrite Zlength_correct in H3' |- *.
  omega.
}
forward. (* n++; *)
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
simpl. normalize. 
subst r_h. simpl.
set (ddlen :=  Zlength dd).
assert (Hddlen: (0 <= ddlen < 64)%Z).
unfold ddlen. split; auto. rewrite Zlength_correct; omega.
repeat rewrite  initial_world.Zlength_map.
forward_if   (invariant_after_if1 hashed dd c md shmd hi lo kv).
* (* then-clause *)
 change Delta with Delta_final_if1.
match goal with |- semax _ _ ?c _ => change c with Body_final_if1 end.
 simpl typeof.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
 make_sequential. rewrite overridePost_normal'.
unfold ddlen in *; clear ddlen.
eapply semax_pre0; [|apply (ifbody_final_if1 Espec hashed md c shmd hi lo dd kv H4 H7 H3 DDbytes)].
entailer!.
unfold_data_at 2%nat.
rewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
rewrite at_offset'_eq by (rewrite <- data_at_offset_zero; reflexivity).
rewrite !map_app.
entailer!.
* (* else-clause *)
forward. (* skip; *)
unfold invariant_after_if1.
normalize. rewrite overridePost_normal'. 
apply exp_right with hashed.
apply exp_right with (dd ++ [128]).
apply exp_right with 0%Z.
entailer.
rewrite mul_repr, sub_repr in H8; apply ltu_repr_false in H8.
2: split; computable.
2: assert (64 < Int.max_unsigned)%Z by computable; unfold ddlen in *;
   split; try omega.
clear TC0.
change (16*4)%Z with (Z.of_nat CBLOCK) in H8.
apply andp_right; [apply prop_right; repeat split | cancel].
rewrite Forall_app; split; auto.
repeat constructor; omega.
rewrite app_length; simpl. apply Nat2Z.inj_ge.
repeat rewrite Nat2Z.inj_add; unfold ddlen in H8; rewrite Zlength_correct in H8.
change (Z.of_nat 1) with 1%Z; change (Z.of_nat 8) with 8%Z.
omega.
f_equal. unfold ddlen; repeat rewrite Zlength_correct; f_equal.
rewrite app_length; simpl. rewrite Nat2Z.inj_add; reflexivity.
unfold_data_at 2%nat.
rewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
rewrite at_offset'_eq by (rewrite <- data_at_offset_zero; reflexivity).
rewrite !map_app.
entailer!.
* unfold invariant_after_if1.
apply extract_exists_pre; intro hashed'.
apply extract_exists_pre; intro dd'.
apply extract_exists_pre; intro pad.
apply semax_extract_PROP; intro DDbytes'.
apply semax_extract_PROP; intro PAD.
normalize.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
unfold sha_finish.
unfold SHA_256.
clear ddlen Hddlen.

    unfold_data_at 1%nat.
    replace (field_at Tsh t_struct_SHA256state_st [StructField _data]
        (map Vint (map Int.repr dd')) c) with
      (field_at Tsh t_struct_SHA256state_st [StructField _data]
        (map Vint (map Int.repr dd') ++ 
         list_repeat (CBLOCK - 8 - length dd')%nat Vundef ++ []) c).
    Focus 2. {
      erewrite field_at_data_equal; [reflexivity | reflexivity |].
      rewrite app_nil_r.
      apply data_equal_sym, data_equal_list_repeat_default.
      reflexivity.
    } Unfocus.
    erewrite array_seg_reroot_lemma
      with (gfs := [StructField _data]) (lo := Zlength dd') (hi := Z.of_nat CBLOCK - 8);
      [| | | reflexivity | | reflexivity | reflexivity | | | reflexivity].
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

forward_call (* memset (p+n,0,SHA_CBLOCK-8-n); *)
  (Tsh,
     offset_val (Int.repr
       (nested_field_offset2 t_struct_SHA256state_st
         [ArraySubsc (Zlength dd'); StructField _data])) c, 
     (Z.of_nat CBLOCK - 8 - Zlength dd')%Z,
     Int.zero).
{
  entailer!.
  + Omega1.
  + erewrite nested_field_offset2_Tarray by reflexivity.
    change (sizeof tuchar) with 1.
    rewrite Z.mul_1_l.
    reflexivity.
  + pull_left (data_at Tsh (Tarray tuchar (Z.of_nat CBLOCK - 8 - Zlength dd') noattr)
     (list_repeat (CBLOCK - 8 - length dd') Vundef)
     (offset_val
        (Int.repr
           (nested_field_offset2 t_struct_SHA256state_st
              [ArraySubsc (Zlength dd'); StructField _data])) c)).
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
    rewrite data_at__memory_block; [| reflexivity | reflexivity |].
    Focus 2. {
       change Int.modulus with 4294967296.
       assert (Z.of_nat CBLOCK = 64) by reflexivity.
       pose proof Zlength_correct dd'.
       omega.
    } Unfocus.
    rewrite H13.
    entailer!.
}
after_call.
normalize.
clear retval0 H11.
(*
  (* after_call manually *)
  cbv beta iota. autorewrite with subst.
replace_SEP 0%Z (`(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0
          (Z.of_nat CBLOCK - 8 - Zlength dd')
          (offset_val (Int.repr (Zlength dd')) (offset_val (Int.repr 40) c)))). {
 entailer!.
}
replace_SEP 7%Z (`(K_vector kv)).
  entailer!.
*)
forward.  (* p += SHA_CBLOCK-8; *)

gather_SEP 0 1 2.
replace_SEP 0 (`(field_at Tsh t_struct_SHA256state_st [StructField _data]
  (map Vint (map Int.repr dd') ++ (list_repeat (Z.to_nat (Z.of_nat CBLOCK - 8 - Zlength dd'))
   (Vint Int.zero)) ++ []) c)).
  {
    erewrite array_seg_reroot_lemma
      with (gfs := [StructField _data]) (lo := Zlength dd') (hi := Z.of_nat CBLOCK - 8);
      [| | | reflexivity | | reflexivity | reflexivity | | | reflexivity].
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
         eapply semax_pre0 with (PROPx nil (LOCALx
          ((`(eq (offset_val (Int.repr
          (nested_field_offset2 t_struct_SHA256state_st
          [ArraySubsc (Z.of_nat CBLOCK - 8); StructField _data])) c)) (eval_id _p))
            :: L) (SEPx S)))
  end.
  Focus 1. {
    entailer!.
    rewrite <- H11.
    destruct (eval_id _c rho); try solve [inversion H13].
    simpl.
    f_equal.
    change (Int.mul (Int.repr 1)
        (Int.sub (Int.mul (Int.repr 16) (Int.repr 4)) (Int.repr 8))) with (Int.repr 56).
    rewrite Int.add_assoc.
    f_equal.
  } Unfocus.
  subst n0.
  drop_LOCAL 2%nat; clear p0.

    


 pose (hibytes := map force_int (map Vint (map Int.repr (intlist_to_Zlist [hi])))).
 pose (lobytes := map force_int (map Vint (map Int.repr (intlist_to_Zlist [lo])))).



STOP.

(**


   semax Delta
     (PROP  ()
      LOCAL 
      (`(eq
           (force_val
              (sem_add_pi tuchar
                 (offset_val
                    (Int.repr
                       (nested_field_offset2 t_struct_SHA256state_st
                          [StructField _data])) c)
                 (Vint
                    (Int.sub (Int.mul (Int.repr 16) (Int.repr 4))
                       (Int.repr 8)))))) (eval_id _p);
      temp _n (Vint (Int.repr (Zlength dd')));
      `(offset_val
          (Int.repr
             (nested_field_offset2 t_struct_SHA256state_st
                [StructField _data])) c = p0); temp _md md; 
      temp _c c; var _K256 (tarray tuint CBLOCKz) kv)
      SEP 
      (`(data_at Tsh (tarray tuchar (Z.of_nat CBLOCK - 8 - Zlength dd'))
           (list_repeat (Z.to_nat (Z.of_nat CBLOCK - 8 - Zlength dd'))
              (Vint Int.zero))
           (offset_val
              (Int.repr
                 (nested_field_offset2 t_struct_SHA256state_st
                    [ArraySubsc (Zlength dd'); StructField _data])) c));
      `(array_at Tsh t_struct_SHA256state_st [StructField _data] 0
          (Zlength dd') (map Vint (map Int.repr dd')) c);
      `(array_at Tsh t_struct_SHA256state_st [StructField _data]
          (Z.of_nat CBLOCK - 8) 64 [] c);
      `(field_at Tsh t_struct_SHA256state_st [StructField _num] Vundef c);
      `(field_at Tsh t_struct_SHA256state_st [StructField _Nh] (Vint hi) c);
      `(field_at Tsh t_struct_SHA256state_st [StructField _Nl] (Vint lo) c);
      `(field_at Tsh t_struct_SHA256state_st [StructField _h]
          (map Vint (hash_blocks init_registers hashed')) c);
      `K_vector (eval_var _K256 (tarray tuint CBLOCKz));
      `(memory_block shmd (Int.repr 32) md)))

**)

 entailer!.
 extract_prop_from_LOCAL.
apply semax_extract_PROP; intro. subst p0.
 replace (`eq (eval_id _p)
      (`(eval_binop Oadd (tptr tuchar) tint) `(offset_val (Int.repr 40) c)
         (`(eval_binop Osub tint tint)
            (`(eval_binop Omul tint tint) `(Vint (Int.repr 16))
               `(Vint (Int.repr 4))) `(Vint (Int.repr 8)))))
  with (temp _p (eval_binop Oadd (tptr tuchar) tint (offset_val (Int.repr 40) c)
                          (Vint (Int.repr (16*4-8)))))
  by normalize.
change data_offset with 40.
change (`(array_at tuchar Tsh
          (fun i : Z =>
           ZnthV tuchar (map Vint (map Int.repr dd'))
             (i + (Z.of_nat CBLOCK - 8))) 0 (64 - (Z.of_nat CBLOCK - 8))
          (offset_val (Int.repr (40 + (Z.of_nat CBLOCK - 8))) c))) with 
   (`(array_at tuchar Tsh (fun i : Z =>
           ZnthV tuchar (map Vint (map Int.repr dd'))
             (i + (Z.of_nat CBLOCK - 8)))
              0 8 (offset_val (Int.repr 96) c))).
replace Delta with Delta_final_if1 by reflexivity.
simpl eval_binop.
change 56 with (16 * 4 - 8).
rewrite offset_offset_val. rewrite add_repr.
normalize.
apply final_part2 with pad; assumption.
Qed.
