Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.verif_sha_update2.
Require Import sha.verif_sha_update3.
Require Import sha.verif_sha_update4.
Require Import sha.call_memcpy.
Local Open Scope nat.
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

Lemma update_last_if_proof:
 forall  (Espec : OracleKind) (hashed : list int) 
           (dd data : list Z) (c d : val) (sh : share) (len : nat) kv
   (H : len <= length data)
   (HBOUND : (bitlength hashed dd + Z.of_nat len * 8 < two_p 64)%Z)
   (c' : name _c)
   (data_ : name _data_)
   (len' : name _len)
   (data' : name _data)
   (p : name _p)
   (n : name _n)
   (fragment : name _fragment)
   (H3 : (Zlength dd < CBLOCKz)%Z)
   (H3' : Forall isbyteZ dd) 
   (H4 : (LBLOCKz | Zlength hashed)%Z)
   (Hlen : (Z.of_nat len <= Int.max_unsigned)%Z)
   (blocks : list int)
   (Hblocks_len : len >= length blocks * 4 - length dd)
   (Hdiv : (LBLOCKz | Zlength blocks)) 
   (Hblocks : intlist_to_Zlist blocks =
          dd ++ firstn (length blocks * 4 - length dd) data)
   (DONE : len - (length blocks * 4 - length dd) < CBLOCK) 
   (Hblocks' : length blocks * 4 >= length dd),
semax
  (initialized _p
     (initialized _n
        (initialized _data (func_tycontext f_SHA256_Update Vprog Gtot))))
  (PROP  ()
   LOCAL  (temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
                temp _c c;
                temp _data (offset_val (Int.repr (Z.of_nat (length blocks * 4 - length dd))) d);
                temp _len (Vint (Int.repr (Z.of_nat (len - (length blocks * 4 - length dd)))));
                gvar  _K256 kv)
   SEP  (`(K_vector kv);
           `(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers (hashed++blocks)),
                  (Vint (lo_part (bitlength hashed dd + (Z.of_nat len)*8)),
                   (Vint (hi_part (bitlength hashed dd + (Z.of_nat len)*8)),
                    (nil, 
                     Vint (Int.repr (Z.of_nat (len - (length blocks * 4 - length dd))))))))
                c);
            `(data_block sh data d)))
  update_last_if
  (normal_ret_assert
     (EX  a' : s256abs,
      PROP  (update_abs (firstn len data) (S256abs hashed dd) a')
      LOCAL (gvar  _K256 kv)
      SEP  (`(K_vector kv);
             `(sha256state_ a' c); `(data_block sh data d)))).
Proof.
  intros.
  unfold update_last_if; simplify_Delta; abbreviate_semax.
  forward_if'.
  + (* then-clause *)
    assert_PROP (Z.of_nat (len - (length blocks * 4 - length dd)) <> 0)%Z. {
      entailer!.
      intro Hz; rewrite Hz in H1; clear Hz. inv H1.
    } drop_LOCAL 0.
    unfold data_block; simpl; normalize.
    rename H0 into Dbytes.
    set (b4d := length blocks * 4 - length dd) in *.
 set (dd' := firstn (len - b4d) (skipn b4d data)).
   assert (H2: Z.of_nat (len-b4d) = Zlength dd'). {
     unfold dd'.
     rewrite Zlength_correct, firstn_length, min_l.
     reflexivity.
     rewrite skipn_length.
     apply minus_le_compat_r.
     omega.
    }
eapply semax_post_flipped3.
*
 assert_PROP (field_compatible (tarray tuchar (Zlength data)) [ArraySubsc (Z.of_nat b4d)] d). {
   entailer.
    rewrite (data_at_field_at sh  (tarray tuchar (Zlength data))).
    rewrite (field_at_compatible' sh).
    entailer!.
    admit.  (* field_compatible_cons *)
  }   
 evar (Frame: list (LiftEnviron mpred)).
  eapply(call_memcpy_tuchar
   (*dst*) Tsh t_struct_SHA256state_st [StructField _data] 0 nil c
   (*src*) sh (tarray tuchar (Zlength data)) [] (Z.of_nat b4d)
                   (map Int.repr data)
                   d
   (*len*) (Z.of_nat (len - b4d))
        Frame); try reflexivity; auto; try omega.
 - rewrite Nat2Z.inj_sub; omega.
 -  rewrite Zlength_nil; omega.
 - simpl. change 64%Z with (Z.of_nat 64). apply Nat2Z.inj_le. change 64 with CBLOCK. omega.
 - rewrite Zlength_map. rewrite <- Nat2Z.inj_add.
  replace (b4d + (len-b4d)) with len by omega.
  split; try omega. rewrite Zlength_correct; apply Nat2Z.inj_le; try omega.
 - 
  unfold_data_at 1. entailer!.
  destruct c; try contradiction.
  unfold field_address.
  rewrite if_true; auto.
  rewrite if_true; auto.
  admit.  (* field_compatible_cons *)
  rewrite field_address_clarify.
  erewrite nested_field_offset2_Tarray; try reflexivity.
  normalize.
  unfold field_address.
  rewrite if_true. destruct d; try contradiction; apply I.
  auto.
* 
 simpl tc_environ; rewrite insert_local.
 clear POSTCONDITION.
replace  (splice_into_list 0 (0 + Z.of_nat (len - b4d)) 64
        (skipn (Z.to_nat (Z.of_nat b4d)) (map Vint (map Int.repr data))) 
        [])
  with (firstn (len - b4d) (skipn b4d (map Vint (map Int.repr data))) ++
           list_repeat (CBLOCK - (len - b4d)) Vundef ).
Focus 2. {
symmetry.
unfold splice_into_list.
change (Z.to_nat 0) with 0. 
rewrite !Z.add_0_l, !Z.sub_0_r, !Nat2Z.id, !app_nil_l.
rewrite skipn_list_repeat
  by (change (Z.to_nat 64) with CBLOCK; clear - DONE; omega).
rewrite (firstn_same _ (Z.to_nat _))
   by (rewrite length_list_repeat; rewrite Z2Nat.inj_sub by omega; rewrite Nat2Z.id; clear; omega).
rewrite firstn_app1
  by (rewrite skipn_length, !map_length; omega).
reflexivity.
} Unfocus.
 unfold data_block.  rewrite prop_true_andp by auto.
 apply exp_right with (S256abs (hashed++blocks) dd').
 unfold sha256state_.
 entailer.
 apply exp_right with 
              (map Vint (hash_blocks init_registers (hashed ++ blocks)),
                (Vint (lo_part (bitlength hashed dd + Z.of_nat len * 8)),
                 (Vint (hi_part (bitlength hashed dd + Z.of_nat len * 8)),
                  (map Vint (map Int.repr dd'), Vint (Int.repr (Zlength dd')))))).
 unfold s256_relate, s256_h, s256_Nh, s256_Nl, s256_data, s256_num.
 simpl @fst; simpl @snd.
assert (bitlength hashed dd + Z.of_nat len * 8 =
            bitlength (hashed ++ blocks) dd')%Z. {
    unfold bitlength, dd'. rewrite (Zlength_correct (firstn _ _)).
    rewrite Zlength_app.
    rewrite firstn_length.
    rewrite skipn_length by omega.
    rewrite min_l  by omega.
    rewrite Nat2Z.inj_sub by omega.
    unfold b4d.
    rewrite Nat2Z.inj_sub by omega.
    repeat rewrite <- Z.mul_add_distr_r.
    rewrite Nat2Z.inj_mul. 
    repeat rewrite <- Zlength_correct.
    change (Z.of_nat 4) with WORD.
    rewrite (Z.mul_add_distr_r _ _ WORD).
    omega.
}
 rewrite H6.
 entailer!.
 -
 apply Update_abs; auto.
 rewrite <- H2; change CBLOCKz with (Z.of_nat CBLOCK);
  apply Nat2Z.inj_lt; assumption.
 rewrite Hblocks.
 repeat rewrite app_ass.
 f_equal.
 unfold dd'; rewrite firstn_app.
 f_equal.
 clear - Hblocks_len; omega.
 -
   rewrite <- H2; change CBLOCKz with (Z.of_nat CBLOCK); apply Nat2Z.inj_lt; auto.
 -
   unfold dd'; apply Forall_firstn; apply Forall_skipn; auto.
-
  rewrite Zlength_app;   apply Z.divide_add_r; auto.
-
   rewrite <- H2.
   unfold_data_at 1. entailer!.
   unfold dd'.
   repeat rewrite skipn_map. repeat rewrite firstn_map.
 apply derives_refl'; apply equal_f; apply field_at_data_equal.
 apply data_equal_sym; apply data_equal_list_repeat_default.
+ (* else-clause *)
 forward. 
 normalize.
 apply exp_right with (S256abs (hashed++blocks) nil).
 entailer.
 rewrite negb_false_iff in H1; apply int_eq_e in H1.
 assert (H2': Int.unsigned (Int.repr (Z.of_nat (len - (length blocks * 4 - length dd)))) = 
              Int.unsigned Int.zero) by (f_equal; apply H1).
 rewrite Int.unsigned_zero in H2'.
 rewrite Int.unsigned_repr in H2'
 by (split; [clear; omega | rewrite Nat2Z.inj_sub by auto; clear - Hlen; omega]).
 assert (H7': len - (length blocks * 4 - length dd) = 0).
   apply Nat2Z.inj. rewrite H2'. reflexivity.
 rewrite H7'. change (Z.of_nat 0) with 0%Z.
 entailer!.
 constructor; auto.
 rewrite <- app_nil_end.
 rewrite Hblocks. f_equal. f_equal. clear - Hblocks_len H7'; omega.
 unfold sha256state_.
 set (bitlen := (bitlength hashed dd + Z.of_nat len * 8)%Z).
 
 apply exp_right with 
              (map Vint (hash_blocks init_registers (hashed ++ blocks)),
                (Vint (lo_part bitlen), 
                 (Vint (hi_part bitlen),
                  (nil, Vint Int.zero)))).
 entailer!.
 unfold s256_relate, s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd.
 simpl.
 unfold bitlen, bitlength.
 rewrite Zlength_nil, Z.add_0_r.
 rewrite Zlength_app.
 rewrite <- (Z.mul_add_distr_r _ _ 8).
 rewrite (Z.mul_add_distr_r _ _ WORD).
 rewrite <- Z.add_assoc.
 replace len with (length blocks * 4 - length dd) by (clear - Hblocks_len H7'; omega).
  rewrite Nat2Z.inj_sub by (clear - Hblocks'; omega).
 rewrite Nat2Z.inj_mul. change (Z.of_nat 4) with WORD.
 rewrite (Zlength_correct blocks), (Zlength_correct dd).
 repeat split; auto. 
 f_equal; f_equal. clear; omega.
 f_equal; f_equal. clear; omega.
 rewrite <- Zlength_correct;  apply Z.divide_add_r; auto.
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
fold sha_update_loop_body in *.
forward.  (* data=data_; *)
assert (LEN: (0 <= s256a_len a)%Z). {
 destruct a; simpl.
 apply Z.mul_nonneg_nonneg; try computable.
 apply Z.add_nonneg_nonneg.
 apply Z.mul_nonneg_nonneg; try computable.
 apply Zlength_nonneg.
 apply Zlength_nonneg.
}
unfold sha256state_. normalize.
intros [r_h [lo' [hi' [r_data r_num]]]].
normalize.
unfold s256_relate in H0.
destruct a as [hashed dd].
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd in H0|-*.
destruct H0 as [H0 [H1 [H8 [[H3 H3'] [H4 H5]]]]].
destruct H1 as [H1 H6].
subst.
unfold_data_at 1%nat.
simpl in LEN.

forward_call' (* SHA256_addlength(c, len); *)
  (len, c, s256a_len (S256abs hashed dd)).
simpl in HBOUND.
repeat split; simpl; try omega.
forward. (* n = c->num; *)
forward. (* p=c->data; *)
fold update_outer_if.
apply semax_seq with (sha_update_inv sh hashed (Z.to_nat len) c d dd data kv false).
* unfold POSTCONDITION, abbreviate.
 eapply semax_pre; [ | simple apply update_outer_if_proof; try assumption].
 - unfold_data_at 1%nat.
   rewrite (field_at_compatible' _ _ [StructField _data]) at 1.
  entailer!.
      apply field_address_clarify; auto.
      rewrite Z2Nat.id by omega; auto.
    rewrite Z2Nat.id by omega; auto.
 - rewrite <- ZtoNat_Zlength. apply Z2Nat.inj_le; auto; omega.
 - rewrite Z2Nat.id by omega; auto.
 - rewrite Z2Nat.id by omega; omega.
* (* after if (n!=0) *)
eapply semax_seq' with
     (sha_update_inv sh hashed (Z.to_nat len) c d dd data kv true).
replace (update_tycon Delta update_outer_if)
   with (initialized _p (initialized _n (initialized _data
                     (func_tycontext f_SHA256_Update Vprog Gtot))))
 by (simplify_Delta; reflexivity).
clear POSTCONDITION MORE_COMMANDS Delta.
simple apply update_while_proof; try assumption.
rewrite <- ZtoNat_Zlength. apply Z2Nat.inj_le; auto; omega.
rewrite Z2Nat.id by omega; auto.
rewrite Z2Nat.id by omega; omega.

simplify_Delta; abbreviate_semax.
unfold sha_update_inv.   apply extract_exists_pre; intro blocks.
apply semax_extract_PROP; apply intro_update_inv; intros.
forward.    (* c->num=len; *)

apply semax_seq with (EX  a' : s256abs,
                    PROP  (update_abs (firstn (Z.to_nat len) data) (S256abs hashed dd) a')
                    LOCAL (gvar  _K256 kv)
                    SEP 
                    (`(K_vector kv);
                     `(sha256state_ a' c); `(data_block sh data d))).

replace Delta with (initialized _p (initialized _n (initialized _data
                     (func_tycontext f_SHA256_Update Vprog Gtot))))
 by (simplify_Delta; reflexivity).
 unfold POSTCONDITION, abbreviate; clear POSTCONDITION Delta MORE_COMMANDS.

make_sequential.
rewrite overridePost_normal'.
fold update_last_if.
rewrite <- data_at_offset_zero.
simpl upd_reptype.
simple apply update_last_if_proof; try assumption.
rewrite <- ZtoNat_Zlength. apply Z2Nat.inj_le; auto; omega.
rewrite Z2Nat.id by omega; auto.
rewrite Z2Nat.id by omega; omega.
abbreviate_semax.
(* after the last if *)
 apply extract_exists_pre; intro a'.
 forward.  (* return; *)
 apply exp_right with a'.
 entailer!.
Qed.
