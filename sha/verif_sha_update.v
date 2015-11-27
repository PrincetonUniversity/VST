Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.verif_sha_update3.
Require Import sha.verif_sha_update4.
Require Import sha.call_memcpy.
Local Open Scope Z.
Local Open Scope logic.

Definition update_last_if :=
  (Sifthenelse (Ebinop One (Etempvar _len tuint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Scall None
                    (Evar _memcpy (Tfunction
                                    (Tcons (tptr tvoid)
                                      (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                    (tptr tvoid) cc_default))
                    ((Etempvar _p (tptr tuchar)) ::
                     (Etempvar _data (tptr tuchar)) ::
                     (Etempvar _len tuint) :: nil))
                  Sskip).

Hint Rewrite @app_nil_l @app_nil_r : sublist.

Lemma update_last_if_proof:
 forall  (Espec : OracleKind) (hashed : list int) 
           (dd data : list Z) (c d : val) (sh : share) (len : Z) kv
   (H : 0 <= len <= Zlength data)
   (Hsh: readable_share sh)
   (HBOUND : (bitlength hashed dd + len * 8 < two_p 64)%Z)
   (c' : name _c)
   (data_ : name _data_)
   (len' : name _len)
   (data' : name _data)
   (p : name _p)
   (n : name _n)
   (fragment : name _fragment)
   (H3 : Zlength dd < CBLOCKz)
   (H3' : Forall isbyteZ dd) 
   (H4 : (LBLOCKz | Zlength hashed))
   (Hlen : len <= Int.max_unsigned)
   (blocks : list int)
   (Hblocks_len : len >= Zlength blocks * 4 - Zlength dd)
   (Hdiv : (LBLOCKz | Zlength blocks)) 
   (Hblocks : intlist_to_Zlist blocks =
          dd ++ sublist 0 (Zlength blocks * 4 - Zlength dd) data)
   (DONE : len - (Zlength blocks * 4 - Zlength dd) < CBLOCKz)
   (Hblocks' : Zlength blocks * 4 >= Zlength dd),
semax
  (initialized_list [_data; _p; _n]
     (func_tycontext f_SHA256_Update Vprog Gtot))
  (PROP  ()
   LOCAL  (temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
                temp _data  (field_address0 (tarray tuchar (Zlength data))
                      [ArraySubsc (Zlength blocks * 4 - Zlength dd)] d);
                temp _c c;
                temp _len (Vint (Int.repr (len - (Zlength blocks * 4 - Zlength dd))));
                gvar  _K256 kv)
   SEP  (K_vector kv;
           data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers (hashed++blocks)),
                  (Vint (lo_part (bitlength hashed dd + len*8)),
                   (Vint (hi_part (bitlength hashed dd + len*8)),
                    (list_repeat (Z.to_nat CBLOCKz) Vundef, 
                     (Vint (Int.repr (len - (Zlength blocks * 4 - Zlength dd))))))))
                c;
            data_block sh data d))
  update_last_if
  (normal_ret_assert
     (PROP  ()
      LOCAL (gvar  _K256 kv)
      SEP  (K_vector kv;
             sha256state_ (S256abs hashed dd ++ sublist 0 len data) c; 
             data_block sh data d))).
Proof.
  intros.
  unfold update_last_if; abbreviate_semax.
 forward_if. 
  + (* then-clause *)
    unfold data_block; simpl; normalize.
    rename H1 into Dbytes.

 set (b4d := Zlength blocks * 4 - Zlength dd) in *.
 assert (BB:  0 <= b4d) by MyOmega.
 set (dd' := sublist b4d len data).
 assert (H2: len - b4d = Zlength dd')
 by (unfold dd'; autorewrite with sublist; MyOmega).
eapply semax_post_flipped3.
*
 assert_PROP (field_compatible0 (tarray tuchar (Zlength data)) [ArraySubsc b4d] d). {
    entailer!.
    auto with field_compatible.
  }   
 evar (Frame: list mpred).
  eapply(call_memcpy_tuchar
   (*dst*) Tsh t_struct_SHA256state_st [StructField _data] 0
                   (list_repeat (Z.to_nat CBLOCKz) Vundef) c
   (*src*) sh (tarray tuchar (Zlength data)) [] b4d
                   (map Int.repr data)
                   d
   (*len*) (len - b4d)
        Frame); try reflexivity; auto; try MyOmega.
 - 
  unfold_data_at 1%nat.
  entailer!.
  make_Vptr c.
  rewrite field_address_offset by auto with field_compatible.
  rewrite field_address0_offset by auto with field_compatible.
  reflexivity.
* 
 assert (Hdiv': (LBLOCKz | Zlength (hashed ++ blocks)))
   by (rewrite Zlength_app; apply Z.divide_add_r; auto).
 simpl tc_environ; rewrite insert_local.
 clear POSTCONDITION.
 pose proof CBLOCKz_eq.
 unfold splice_into_list; autorewrite with sublist.
 unfold data_block.  rewrite prop_true_andp by auto.
(* Exists (S256abs (hashed++blocks) dd'). *)
 unfold sha256state_.
 Exists    (map Vint (hash_blocks init_registers (hashed ++ blocks)),
                (Vint (lo_part (bitlength hashed dd + len * 8)),
                 (Vint (hi_part (bitlength hashed dd + len * 8)),
                  (map Vint (map Int.repr dd') ++ list_repeat (Z.to_nat (64-(len-b4d))) Vundef, 
                   Vint (Int.repr (Zlength dd')))))).
 pose proof (update_abs_eq  (sublist 0 len data) (S256abs hashed dd)
                     (S256abs (hashed++blocks) dd')).
 destruct H5 as [_ ?].
 apply Forall_app; split; auto.
 apply Forall_app; split; auto.
 apply isbyte_intlist_to_Zlist.
 apply Forall_app; split; auto.
 apply isbyte_intlist_to_Zlist.
 subst dd'; auto.
 unfold update_abs in H5. rewrite <- H5.
Focus 2. {
 exists blocks.
 rewrite !S256abs_hashed; auto; try omega.
 rewrite !S256abs_data; auto; try omega.
 split; auto.
 rewrite Hblocks. unfold dd'. rewrite app_ass.
 f_equal.
 rewrite (sublist_split 0 b4d len); auto; omega.
 } Unfocus.
assert (Hbb: bitlength hashed dd + len * 8 =
            bitlength (hashed ++ blocks) dd'). {
    unfold bitlength, dd'.
   autorewrite with sublist.
    unfold b4d.
    rewrite <- !Z.mul_add_distr_r.
    change 4%Z with WORD.
    rewrite (Z.mul_add_distr_r _ _ WORD).
    omega.        
}
 rewrite Hbb.
 entailer!.
hnf.  unfold s256_h, s256_data, s256_num, s256_Nh, s256_Nl, s256a_regs, fst, snd.
 rewrite <- bitlength_eq.
 rewrite !S256abs_hashed; auto; try omega.
 rewrite !S256abs_data; auto; try omega.
 split3; auto.
 split; auto.
 autorewrite with sublist; auto.
 split; auto.
 apply Forall_app; split; auto.
 apply isbyte_intlist_to_Zlist.
 subst dd'; auto.
 unfold_data_at 1%nat.
 rewrite H2.
 cancel. unfold dd'. rewrite !sublist_map. cancel.
+ (* else-clause *)
 assert (H4': (LBLOCKz | Zlength (hashed ++ blocks))%Z)
   by (rewrite Zlength_app; apply Z.divide_add_r; auto).
 forward.
 unfold sha256state_.
 entailer!.
 eapply exp_right. apply andp_right; [ | apply derives_refl]. 
 apply prop_right.
 pose proof (update_abs_eq  (sublist 0 len data) (S256abs hashed dd)
                     (S256abs (hashed++blocks) nil)).
 destruct H9 as [_ ?].
 apply Forall_app; split; auto.
 apply Forall_app; split; auto.
 apply isbyte_intlist_to_Zlist.
 apply Forall_app; split; auto.
 apply isbyte_intlist_to_Zlist.
 unfold update_abs in H9. rewrite <- H9.
Focus 2. {
 exists blocks.
 rewrite !S256abs_hashed; auto; try omega.
 rewrite !S256abs_data; auto; try omega.
 split; auto.
 rewrite Hblocks. rewrite <- app_nil_end.
 f_equal.
 f_equal; omega.
 } Unfocus.
 clear H9.
 hnf.  unfold s256_relate, s256_h, s256_Nh,s256_Nl, s256_num, s256_data, s256a_regs, fst,snd.
 rewrite !S256abs_hashed; auto; try omega.
 rewrite !S256abs_data; auto; try omega.
 rewrite <- bitlength_eq.
 replace (bitlength hashed dd + len * 8) 
  with (bitlength (hashed ++ blocks) []).
 split3; auto.
 split3; auto.
 apply Forall_app; split.
 apply isbyte_intlist_to_Zlist.
 constructor.
 f_equal. f_equal.
 rewrite Zlength_nil; omega.
 unfold bitlength.
 rewrite <- (Z.mul_add_distr_r _ _ 8).
 rewrite Zlength_nil, Z.add_0_r.
 rewrite Zlength_app.
 rewrite (Z.mul_add_distr_r _ _ WORD).
 rewrite <- Z.add_assoc.
 replace len with (Zlength blocks * 4 - Zlength dd) by omega.
 change 4%Z with WORD.
 repeat split; auto; try now (f_equal; f_equal; clear; omega).
Qed.

Lemma overridePost_derives:
  forall F F' G G' ek vl,
     F |-- F'  ->
     G ek vl |-- G' ek vl ->
     overridePost F G ek vl |-- overridePost F' G' ek vl.
Proof.
intros.
unfold overridePost.
if_tac.
apply andp_derives; auto.
auto.
Qed.

Lemma function_body_ret_assert_derives:
  forall F F' t ek vl,
   F |-- F' ->
  function_body_ret_assert t F ek vl 
    |-- function_body_ret_assert t F' ek vl.
Proof.
intros.
unfold function_body_ret_assert.
destruct ek; auto.
unfold bind_ret.
destruct vl; auto.
apply andp_derives; auto.
unfold_lift. intro rho. apply H.
destruct t; auto.
intro rho. apply H.
Qed.

Lemma body_SHA256_Update: semax_body Vprog Gtot f_SHA256_Update SHA256_Update_spec.
Proof.
start_function.
name c' _c.
name data_ _data_.
name len' _len.
name data' _data.
name p _p.
name n _n.
name fragment _fragment.
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
destruct H0 as [H0 [[H1 H6] [H8 [H3 H4]]]].
subst.

unfold_data_at 1%nat.
forward_call (* SHA256_addlength(c, len); *)
  (len, c, s256a_len (S256abs (s256a_hashed a) (s256a_data a))).
 rewrite S256abs_recombine by auto.
 cancel.
 rewrite S256abs_recombine by auto.
 repeat split; simpl; try omega.
 apply HBOUND.
(* TODO:  need a fold_data_at tactic; the next few lines do that here *)
gather_SEP' [5;0;1;3;4]%Z.
 rewrite <- bitlength_eq.
replace_SEP 0 (data_at Tsh t_struct_SHA256state_st
    (map Vint (hash_blocks init_registers (s256a_hashed a)),
        (Vint (lo_part (bitlength (s256a_hashed a) (s256a_data a) + len * 8)),
        (Vint (hi_part (bitlength (s256a_hashed a) (s256a_data a) + len * 8)),
        (map Vint (map Int.repr (s256a_data a))++ 
         list_repeat (Z.to_nat (CBLOCKz - Zlength (s256a_data a))) Vundef,
         Vint (Int.repr (Zlength (s256a_data a))))))) c). {
  unfold_data_at 1%nat; entailer!.
  assert (legal_nested_field t_struct_SHA256state_st [StructField _data]).
    apply compute_legal_nested_field_spec'; repeat constructor.
  erewrite field_at_Tarray; try reflexivity; auto.
  erewrite field_at_Tarray; try reflexivity; auto.
  rewrite <- H8.
  simplify_value_fits in H13. destruct H13.
  pose proof (s256a_data_Zlength_less a).
  rewrite (split2_array_at _ _ _ 0 (Zlength (s256a_data a)) 64) by (auto; Omega1).
  rewrite (split2_array_at _ _ _ 0 (Zlength (s256a_data a)) 64).
  2: Omega1.
  Focus 2. {
    autorewrite with sublist.
    rewrite Zlength_sublist by Omega1. Omega1.
  } Unfocus.
  change (@reptype CompSpecs tuchar) with val in H13. (* should not need this! *)
  pose proof CBLOCKz_eq.
  pose proof (Zlength_nonneg (s256a_data a)).
  autorewrite with sublist.
  change (@reptype CompSpecs tuchar) with val. (* should not need this! *)
 change ( (@reptype CompSpecs
           (@nested_field_type CompSpecs t_struct_SHA256state_st
              [ArraySubsc 0; StructField _data]))) with val.
  rewrite H13.
  cancel. 
  apply derives_trans with (array_at_ Tsh t_struct_SHA256state_st [StructField _data] (Zlength (s256a_data a)) 64 c');
     [ cancel | apply derives_refl].
}
(* end of TODO *)
forward. (* n = c->num; *)
forward. (* p=c->data; *)
    (* TODO: should this produce field_address instead of (Int.repr 40) ? *)
assert_PROP (field_address t_struct_SHA256state_st [StructField _data] c
          = offset_val (Int.repr 40) c).
  unfold_data_at 1%nat.
 rewrite (field_at_compatible' _ _ [StructField _data]).
  entailer!.
 normalize.
 rewrite <- H0.
apply semax_seq with (sha_update_inv sh (s256a_hashed a) len c d (s256a_data a) data kv false).
*
 semax_subcommand Vprog Gtot  f_SHA256_Update.
 eapply semax_post;
   [ | simple apply update_outer_if_proof; try eassumption; auto; try omega].
 intros; apply andp_left2.
 rewrite S256abs_recombine.
 apply overridePost_derives; auto.
 apply function_body_ret_assert_derives.
 Intros a'. rewrite H1. auto.
 auto.
 rewrite bitlength_eq, S256abs_recombine; auto.
 apply s256a_data_Zlength_less.
 apply Forall_sublist; auto.
 apply s256a_hashed_divides.
* (* after if (n!=0) *)
 eapply semax_seq' with
     (sha_update_inv sh (s256a_hashed a) len c d (s256a_data a) data kv true).
 semax_subcommand Vprog Gtot  f_SHA256_Update.
simple apply update_while_proof; try assumption; try omega; auto.
 rewrite bitlength_eq, S256abs_recombine; auto.
 apply s256a_data_Zlength_less.
 apply Forall_sublist; auto.
 apply s256a_hashed_divides.

abbreviate_semax.
unfold sha_update_inv.   apply extract_exists_pre; intro blocks.
forward.    (* c->num=len; *)

apply semax_seq with (
                    PROP  ()
                    LOCAL (gvar  _K256 kv)
                    SEP 
                    (K_vector kv;
                     sha256state_ (S256abs (s256a_hashed a) (s256a_data a) ++ sublist 0 len data) c; data_block sh data d)).

make_sequential.
 semax_subcommand Vprog Gtot  f_SHA256_Update.
fold update_last_if.
pose proof (Hblocks_lem H4).
assert_PROP (isptr c) by entailer!.
rewrite isptr_offset_val_zero by auto.
change (field_at  Tsh t_struct_SHA256state_st [])
  with (data_at Tsh t_struct_SHA256state_st).

simple apply update_last_if_proof; try assumption; try omega.
 rewrite bitlength_eq, S256abs_recombine; auto.
 apply s256a_data_Zlength_less.
 apply Forall_sublist; auto.
 apply s256a_hashed_divides.
abbreviate_semax.
(* after the last if *)
 forward.  (* return; *)
 rewrite S256abs_recombine; auto.
Qed.
