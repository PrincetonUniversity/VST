Require Import VST.floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.verif_sha_update3.
Require Import sha.verif_sha_update4.
Require Import sha.call_memcpy.
Local Open Scope Z.

Lemma body_SHA256_Update: semax_body Vprog Gtot f_SHA256_Update SHA256_Update_spec.
Proof.
start_function.
rename H0 into HBOUND'.
rename H1 into HBOUND.

fold update_inner_if_then in *.
fold update_inner_if_else in *.
fold update_inner_if in *.
fold update_outer_if in *.
fold sha_update_loop_body in *.
forward.  (* data=data_; *)
assert (LEN: 0 <= s256a_len a). {
 unfold s256a_len.
 apply Z.mul_nonneg_nonneg; try computable.
 apply Zlength_nonneg.
}
unfold sha256state_.
Intros r; destruct r as [r_h [lo' [hi' [r_data r_num]]]].
unfold s256_relate in H0.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd in H0|-*.
destruct H0 as [H0 [[H1 H6] [H8 H4]]].
assert (H3:=I).
subst.

unfold_data_at (data_at _ _ _ _).
forward_call (* SHA256_addlength(c, len); *)
  (len, c, wsh, s256a_len a).
(* TODO:  need a fold_data_at tactic; the next few lines do that here *)
gather_SEP' [5;0;1;3;4]%Z.
replace_SEP 0 (data_at wsh t_struct_SHA256state_st
    (map Vint (hash_blocks init_registers (s256a_hashed a)),
        (Vint (lo_part (s256a_len a + len * 8)),
        (Vint (hi_part (s256a_len a + len * 8)),
        (map Vubyte (s256a_data a)++
         repeat Vundef (Z.to_nat (CBLOCKz - Zlength (s256a_data a))),
         Vint (Int.repr (Zlength (s256a_data a))))))) c). {
  unfold_data_at (data_at _ _ _ _); entailer!.
  assert (legal_nested_field t_struct_SHA256state_st [StructField _data]).
    apply compute_legal_nested_field_spec'; repeat constructor.
  erewrite field_at_Tarray; try apply JMeq_refl; try reflexivity; [ | auto..].
  erewrite field_at_Tarray; try apply JMeq_refl; try reflexivity; [ | auto..].
  rewrite <- H8; clear H8.
  assert (H8 := s256a_data_Zlength_less a).
  simplify_value_fits in H11. destruct H11 as [H11 _].
  change (@reptype CompSpecs tuchar) with val in H11. (* should not need this! *)
  rewrite (split2_array_at _ _ _ 0 (Zlength (s256a_data a)) 64) by (auto; Omega1).
  rewrite (split2_array_at _ _ _ 0 (Zlength (s256a_data a)) 64).
  2: Omega1.
  2:{
    autorewrite with sublist.
    rewrite Zlength_sublist by Omega1. Omega1.
  }
  pose proof CBLOCKz_eq.
  pose proof (Zlength_nonneg (s256a_data a)).
  autorewrite with sublist.
  change (@reptype CompSpecs tuchar) with val. (* should not need this! *)
 change ( (@reptype CompSpecs
           (@nested_field_type CompSpecs t_struct_SHA256state_st
              [ArraySubsc 0; StructField _data]))) with val.
  rewrite H11.
  cancel.
  apply derives_trans with (array_at_ wsh t_struct_SHA256state_st [StructField _data] (Zlength (s256a_data a)) 64 c);
     [ cancel | apply derives_refl].
}
(* end of TODO *)
forward. (* n = c->num; *)
forward. (* p=c->data; *)
simpl (temp _p _).
    (* TODO: should this produce field_address instead of (Int.repr 40) ? *)
assert_PROP (field_address t_struct_SHA256state_st [StructField _data] c = offset_val 40 c).
  unfold_data_at (data_at _ _ _ _).
  rewrite (field_at_compatible' _ _ [StructField _data]).
  entailer!.
  normalize.
rewrite <- H0.
clear H0; pose (H0:=True%type).
apply semax_seq with (sha_update_inv wsh sh (s256a_hashed a) len c d (s256a_data a) data gv false).
* semax_subcommand Vprog Gtot f_SHA256_Update (@nil (ident * Annotation)).
 eapply semax_post_flipped.
+
 assert (BLEN: bitlength (s256a_hashed a) (s256a_data a) = s256a_len a)
   by (rewrite bitlength_eq, S256abs_recombine; auto).
 pattern (s256a_len a + len * 8); rewrite <- BLEN at 1.
 simple apply update_outer_if_proof; try eassumption; auto; try lia.
 apply s256a_data_Zlength_less.
 apply s256a_hashed_divides.
+ simpl_ret_assert; apply ENTAIL_refl.
+ simpl_ret_assert; apply ENTAIL_refl.
+ simpl_ret_assert; apply ENTAIL_refl.
+ intros; simpl_ret_assert.
 rewrite S256abs_recombine by auto.
 apply andp_left2.
 apply bi.sep_mono; last cancel.
 apply bind_ret_derives.
 Intros a'.
 apply derives_extract_PROP'; intro. (* this should be done a better way *)
 rewrite H1. auto.
* (* after if (n!=0) *)
 eapply semax_seq' with
     (sha_update_inv wsh sh (s256a_hashed a) len c d (s256a_data a) data gv true).
 semax_subcommand Vprog Gtot  f_SHA256_Update (@nil (ident * Annotation)).
simple apply update_while_proof; try assumption; try lia; auto.
 rewrite bitlength_eq, S256abs_recombine; auto.
 apply s256a_data_Zlength_less.
 apply s256a_hashed_divides.

abbreviate_semax.
unfold sha_update_inv.   apply extract_exists_pre; intro blocks.
forward.    (* c->num=len; *)

assert (H6 := Hblocks_lem H4).
set (dd := s256a_data a) in *.
set (hashed := s256a_hashed a) in *.
unfold data_block. simpl. Intros.
rename H1 into Dbytes.
rename H3 into H3x;
assert (H3 : Zlength dd < CBLOCKz) by apply s256a_data_Zlength_less.
replace (s256a_len a) with (bitlength hashed dd) in HBOUND
   by (subst dd hashed; rewrite bitlength_eq, S256abs_recombine; auto).
set (b4d := Zlength blocks * 4 - Zlength dd) in *.
rename H into Hx; assert (H: 0 <= len <= Zlength data) by lia; clear Hx LEN.
rename H4 into Hblocks;
assert (H4 : (LBLOCKz | Zlength hashed)) by apply s256a_hashed_divides.
assert (BB:  0 <= b4d) by MyOmega.
assert (UAE: S256abs (hashed ++ blocks) (sublist b4d len data) =
      S256abs hashed dd ++ sublist 0 len data). {
 apply update_abs_eq.
 exists blocks.
 rewrite !S256abs_hashed
   by (try apply divide_length_app; auto; autorewrite with sublist; auto).
 split; auto.
 rewrite Hblocks. rewrite <- app_assoc.
 rewrite !S256abs_data
   by (try apply divide_length_app; auto; autorewrite with sublist; auto).
 f_equal.
 rewrite (sublist_split 0 b4d len) by (auto; lia).
 auto.
 }
forward_if (   PROP  ()
                    LOCAL (gvars  gv)
                    SEP
                    (K_vector gv;
                     sha256state_ wsh (S256abs hashed dd ++ sublist 0 len data) c; data_block sh data d)).
+ (* then-clause *)
    set (dd' := sublist b4d len data).
    rename H2 into Hdiv.
    assert (H2: len - b4d = Zlength dd')
      by (unfold dd'; autorewrite with sublist; MyOmega).
    make_sequential.
    unfold_data_at (data_at _ _ _ c).
    freeze FR1 := -(field_at(cs := CompSpecs) wsh t_struct_SHA256state_st (DOT _data) (repeat Vundef (Z.to_nat CBLOCKz)) c)
      (data_at sh (tarray tuchar (Zlength data)) (map Vubyte data) d).
    eapply semax_post_flipped3.
  - assert_PROP (field_compatible0 (tarray tuchar (Zlength data)) [ArraySubsc b4d] d)
      by (entailer!; auto with field_compatible).
  eapply(call_memcpy_tuchar
   (*dst*) wsh t_struct_SHA256state_st [StructField _data] 0
                   (repeat Vundef (Z.to_nat CBLOCKz)) c
   (*src*) sh (tarray tuchar (Zlength data)) [] b4d
                   (map Int.repr (map Byte.unsigned data))
                   d
   (*len*) (len - b4d)
        [FRZL FR1]); try reflexivity; auto; try MyOmega.
  entailer!.
  rewrite map_Vubyte_eq'. cancel.
 -
 thaw' FR1; simpl.
 subst POSTCONDITION; unfold abbreviate. simpl_ret_assert.
 pose proof CBLOCKz_eq.
 unfold splice_into_list; autorewrite with sublist.
 unfold data_block.
 unfold sha256state_.
 Exists    (map Vint (hash_blocks init_registers (hashed ++ blocks)),
                (Vint (lo_part (bitlength hashed dd + len * 8)),
                 (Vint (hi_part (bitlength hashed dd + len * 8)),
                  (map Vubyte dd' ++ repeat Vundef (Z.to_nat (64-(len-b4d))),
                   Vint (Int.repr (Zlength dd')))))).
 rewrite <- UAE.
assert (Hbb: bitlength hashed dd + len * 8 =
            bitlength (hashed ++ blocks) dd'). {
    unfold bitlength, dd'.
   autorewrite with sublist.
    unfold b4d.
    rewrite <- !Z.mul_add_distr_r.
    change 4%Z with WORD.
    rewrite (Z.mul_add_distr_r _ _ WORD).
    lia.
}
 rewrite Hbb.
 entailer!.
hnf.  unfold s256_h, s256_data, s256_num, s256_Nh, s256_Nl, s256a_regs, fst, snd.
 rewrite <- bitlength_eq.
 autorewrite with sublist.
 rewrite !S256abs_hashed
   by (try apply divide_length_app; auto; autorewrite with sublist; auto).
 rewrite !S256abs_data
   by (try apply divide_length_app; auto; autorewrite with sublist; auto).
 split3; auto.
 split; auto.
 autorewrite with sublist; auto.
 unfold_data_at (data_at _ _ _ c).
 rewrite H2. rewrite !sublist_map.
 rewrite !map_Vubyte_eq'.
 cancel.
 subst dd'.
 autorewrite with sublist.
 replace (b4d + (len - b4d)) with len by lia.
 cancel.
+ (* else-clause *)
 forward. (* skip; *)
 try (fold dd in H1; fold b4d in H1; apply repr_inj_unsigned in H1; try rep_lia).
 unfold sha256state_.
 unfold data_block.
 match goal with |- context [data_at _ t_struct_SHA256state_st ?r _] => Exists r end.
 entailer!.
 rewrite <- UAE.
 autorewrite with sublist.
 hnf.  unfold s256_relate, s256_h, s256_Nh,s256_Nl, s256_num, s256_data, s256a_regs, fst,snd.
 rewrite !S256abs_hashed
   by (try apply divide_length_app; auto; autorewrite with sublist; auto).
 rewrite !S256abs_data
   by (try apply divide_length_app; auto; autorewrite with sublist; auto).
 rewrite <- bitlength_eq.
 replace (bitlength hashed dd + len * 8)
  with (bitlength (hashed ++ blocks) []).
 split3; auto.
 split; auto.
 f_equal. f_equal.
 rewrite Zlength_nil; lia.
 unfold bitlength.
 rewrite <- (Z.mul_add_distr_r _ _ 8).
 f_equal.
 rewrite Zlength_nil, Z.add_0_r.
 rewrite Zlength_app.
 rewrite (Z.mul_add_distr_r _ _ WORD).
 rewrite <- Z.add_assoc.
 f_equal.
 replace len with b4d by lia. unfold b4d.
 change 4%Z with WORD. lia.
+
(* after the last if *)
 forward.  (* return; *)
 subst hashed dd.
 rewrite S256abs_recombine; auto.
Qed.
