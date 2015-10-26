Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.verif_sha_update2.
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
   SEP  (`(K_vector kv);
           `(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers (hashed++blocks)),
                  (Vint (lo_part (bitlength hashed dd + len*8)),
                   (Vint (hi_part (bitlength hashed dd + len*8)),
                    (list_repeat (Z.to_nat CBLOCKz) Vundef, 
                     (Vint (Int.repr (len - (Zlength blocks * 4 - Zlength dd))))))))
                c);
            `(data_block sh data d)))
  update_last_if
  (normal_ret_assert
     (EX  a' : s256abs,
      PROP  (update_abs (sublist 0 len data) (S256abs hashed dd) a')
      LOCAL (gvar  _K256 kv)
      SEP  (`(K_vector kv);
             `(sha256state_ a' c); `(data_block sh data d)))).
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
    eapply field_compatible0_cons_Tarray; try reflexivity; auto; omega.
  }   
 evar (Frame: list (LiftEnviron mpred)).
  eapply(call_memcpy_tuchar
   (*dst*) Tsh t_struct_SHA256state_st [StructField _data] 0
                   (list_repeat (Z.to_nat CBLOCKz) Vundef) c
   (*src*) sh (tarray tuchar (Zlength data)) [] b4d
                   (map Int.repr data)
                   d
   (*len*) (len - b4d)
        Frame); try reflexivity; auto; try MyOmega.
 - 
  unfold data_at at 1.   unfold_field_at 1%nat.
  entailer!.
  make_Vptr c.
  unfold field_address, field_address0.
  rewrite if_true; auto.
  rewrite if_true; auto.
  eapply field_compatible0_cons_Tarray; try reflexivity; auto; omega.
* 
 simpl tc_environ; rewrite insert_local.
 clear POSTCONDITION.
 pose proof CBLOCKz_eq.
 unfold splice_into_list; autorewrite with sublist.
 unfold data_block.  rewrite prop_true_andp by auto.
 Exists (S256abs (hashed++blocks) dd').
 unfold sha256state_.
 entailer!.
 constructor; auto; try Omega1.
 rewrite Hblocks. unfold dd'. rewrite app_ass.
 f_equal.
 rewrite (sublist_split 0 b4d len); auto; omega.
 Exists    (map Vint (hash_blocks init_registers (hashed ++ blocks)),
                (Vint (lo_part (bitlength hashed dd + len * 8)),
                 (Vint (hi_part (bitlength hashed dd + len * 8)),
                  (map Vint (map Int.repr dd') ++ list_repeat (Z.to_nat (64-(len-b4d))) Vundef, 
                   Vint (Int.repr (Zlength dd')))))).
 simpl.
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
 unfold s256_data, dd'; simpl. autorewrite with sublist.
 split3; auto. apply Forall_sublist; auto.
 apply Z.divide_add_r; auto.
   rewrite <- H2.
   unfold data_at; unfold_field_at 6%nat. entailer!.
   unfold dd'.
   rewrite !sublist_map; auto.
+ (* else-clause *)
 forward. 
 normalize.
 Exists (S256abs (hashed++blocks) nil).
 entailer!.
 constructor; auto. rewrite Hblocks.
 autorewrite with sublist. f_equal. f_equal. omega.
 unfold sha256state_.
 set (bitlen := bitlength hashed dd + len * 8).
 eapply exp_right. apply andp_right; [ | apply derives_refl]. 
 entailer!.
 unfold s256_relate, s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd.
 simpl.
 split; auto.
 unfold bitlen, bitlength.
 autorewrite with sublist.
 rewrite <- (Z.mul_add_distr_r _ _ 8).
 rewrite (Z.mul_add_distr_r _ _ WORD).
 rewrite <- Z.add_assoc.
 replace len with (Zlength blocks * 4 - Zlength dd) by omega.
 change 4%Z with WORD.
 repeat split; auto; try now (f_equal; f_equal; clear; omega).
 apply Z.divide_add_r; auto.
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
 destruct a; simpl.
 unfold bitlength. change WORD with 4.
 apply Z.mul_nonneg_nonneg; try computable.
 apply Z.add_nonneg_nonneg.
 apply Z.mul_nonneg_nonneg; try computable.
 apply Zlength_nonneg.
 apply Zlength_nonneg.
}
unfold sha256state_.
normalize.
intros [r_h [lo' [hi' [r_data r_num]]]].
normalize.
unfold s256_relate in H0.
destruct a as [hashed dd].
simpl in LEN, HBOUND.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd in H0|-*.
destruct H0 as [H0 [H1 [H8 [[H3 H3'] [H4 H5]]]]].
destruct H1 as [H1 H6].
subst.

unfold data_at; unfold_field_at 1%nat.
forward_call (* SHA256_addlength(c, len); *)
  (len, c, s256a_len (S256abs hashed dd)).
  repeat split; simpl; omega.
(* TODO:  need a fold_data_at tactic; the next few lines do that here *)
gather_SEP' [4;0;1;2;3]%Z.
replace_SEP 0 `(data_at Tsh t_struct_SHA256state_st
    (map Vint (hash_blocks init_registers hashed),
        (Vint (lo_part (bitlength hashed dd + len * 8)),
        (Vint (hi_part (bitlength hashed dd + len * 8)),
        (map Vint (map Int.repr dd)++ 
         list_repeat (Z.to_nat (CBLOCKz - Zlength dd)) Vundef,
         Vint (Int.repr (Zlength dd)))))) c). {
  unfold data_at; unfold_field_at 6%nat; entailer!.
  assert (legal_nested_field t_struct_SHA256state_st [StructField _data]).
    apply compute_legal_nested_field_spec'; repeat constructor.
  erewrite field_at_Tarray; try reflexivity; auto.
  erewrite field_at_Tarray; try reflexivity; auto.
  rewrite <- H8.
  rewrite (split2_array_at _ _ _ 0 (Zlength dd) 64) by Omega1.
  rewrite (split2_array_at _ _ _ 0 (Zlength dd) 64) by Omega1.
  simplify_value_fits in H14. destruct H14.
  change (@reptype CompSpecs tuchar) with val in H14. (* should not need this! *)
  pose proof CBLOCKz_eq.
  pose proof (Zlength_nonneg dd).
  autorewrite with sublist.
  rewrite H17.
  cancel.
  apply derives_trans with (array_at_ Tsh t_struct_SHA256state_st [StructField _data] (Zlength dd) 64 c');
     cancel.
}
(* end of TODO *)
forward. (* n = c->num; *)
forward. (* p=c->data; *)
    (* TODO: should this produce field_address instead of (Int.repr 40) ? *)
assert_PROP (field_address t_struct_SHA256state_st [StructField _data] c
          = offset_val (Int.repr 40) c).
  unfold data_at; unfold_field_at 1%nat; rewrite (field_at_compatible' _ _ [StructField _data]).
  entailer!.
rewrite <- H0.
apply semax_seq with (sha_update_inv sh hashed len c d dd data kv false).
*
 semax_subcommand Vprog Gtot  f_SHA256_Update.
 simple apply update_outer_if_proof; try assumption; omega.
* (* after if (n!=0) *)
 eapply semax_seq' with
     (sha_update_inv sh hashed len c d dd data kv true).
 semax_subcommand Vprog Gtot  f_SHA256_Update.
simple apply update_while_proof; try assumption.
omega.
omega.

abbreviate_semax.
unfold sha_update_inv.   apply extract_exists_pre; intro blocks.
normalize.
forward.    (* c->num=len; *)

apply semax_seq with (EX  a' : s256abs,
                    PROP  (update_abs (sublist 0 len data) (S256abs hashed dd) a')
                    LOCAL (gvar  _K256 kv)
                    SEP 
                    (`(K_vector kv);
                     `(sha256state_ a' c); `(data_block sh data d))).

make_sequential.
 semax_subcommand Vprog Gtot  f_SHA256_Update.
fold update_last_if.
pose proof (Hblocks_lem H5).
assert_PROP (isptr c) by entailer!.
rewrite isptr_offset_val_zero by auto.
change (field_at  Tsh t_struct_SHA256state_st [])
  with (data_at Tsh t_struct_SHA256state_st).
simple apply update_last_if_proof; try assumption; try omega.
abbreviate_semax.
(* after the last if *)
 Intro a'.
 forward.  (* return; *)
 Exists a'.
 entailer!.
Qed.
