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
           (dd data : list Z) (c d : val) (sh : share) (len : Z) kv
   (H : (0 <= len <= Zlength data)%Z)
   (HBOUND : (bitlength hashed dd + len * 8 < two_p 64)%Z)
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
   (Hlen : (len <= Int.max_unsigned)%Z)
   (blocks : list int)
   (Hblocks_len : (len >= Zlength blocks * 4 - Zlength dd)%Z)
   (Hdiv : (LBLOCKz | Zlength blocks)) 
   (Hblocks : intlist_to_Zlist blocks =
          dd ++ firstn (length blocks * 4 - length dd) data)
   (DONE : (len - (Zlength blocks * 4 - Zlength dd) < CBLOCKz)%Z)
   (Hblocks' : (Zlength blocks * 4 >= Zlength dd)%Z),
semax
  (initialized_list [_p; _n; _data]
     (func_tycontext f_SHA256_Update Vprog Gtot))
  (PROP  ()
   LOCAL  (temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
                temp _data (offset_val (Int.repr (Zlength blocks * 4 - Zlength dd)) d);
                temp _c c;
                temp _len (Vint (Int.repr (len - (Zlength blocks * 4 - Zlength dd))));
                gvar  _K256 kv)
   SEP  (`(K_vector kv);
           `(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers (hashed++blocks)),
                  (Vint (lo_part (bitlength hashed dd + len*8)),
                   (Vint (hi_part (bitlength hashed dd + len*8)),
                    (nil, 
                     (Vint (Int.repr (len - (Zlength blocks * 4 - Zlength dd))))))))
                c);
            `(data_block sh data d)))
  update_last_if
  (normal_ret_assert
     (EX  a' : s256abs,
      PROP  (update_abs (firstn (Z.to_nat len) data) (S256abs hashed dd) a')
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

 set (b4d := (Zlength blocks * 4 - Zlength dd)%Z) in *.
 assert (BB:  (0 <= b4d)%Z) by MyOmega.
 set (dd' := firstn (Z.to_nat (len - b4d)) (skipn (Z.to_nat b4d) data)).
 assert (H2: (len - b4d = Zlength dd')%Z)
 by (unfold dd'; rewrite Zlength_correct, firstn_length, min_l; MyOmega).
eapply semax_post_flipped3.
*
 assert_PROP (field_compatible0 (tarray tuchar (Zlength data)) [ArraySubsc b4d] d). {
   entailer.
    rewrite (data_at_field_at sh  (tarray tuchar (Zlength data))).
    rewrite (field_at_compatible' sh).
    entailer!.
    eapply field_compatible0_cons_Tarray.
    reflexivity. auto. omega.
  }   
 evar (Frame: list (LiftEnviron mpred)).
  eapply(call_memcpy_tuchar
   (*dst*) Tsh t_struct_SHA256state_st [StructField _data] 0 nil c
   (*src*) sh (tarray tuchar (Zlength data)) [] b4d
                   (map Int.repr data)
                   d
   (*len*) (len - b4d)
        Frame); try reflexivity; auto; try MyOmega.
 - 
  unfold_data_at 1. entailer!.
  destruct c; try contradiction.
  unfold field_address, field_address0.
  rewrite if_true; auto.
  rewrite if_true; auto.
  eapply field_compatible0_cons_Tarray.
    reflexivity. auto. omega.
  rewrite field_address0_clarify.
  erewrite nested_field_offset2_Tarray; try reflexivity.
  normalize.
  unfold field_address0.
  rewrite if_true. destruct d; try contradiction; apply I.
  auto.
* 
 simpl tc_environ; rewrite insert_local.
 clear POSTCONDITION.
replace  (splice_into_list 0 (0 + (len - b4d)) 64
        (skipn (Z.to_nat b4d) (map Vint (map Int.repr data))) 
        [])
  with (firstn (Z.to_nat (len - b4d)) (skipn (Z.to_nat b4d) (map Vint (map Int.repr data))) ++
           list_repeat (CBLOCK - (Z.to_nat (len - b4d))) Vundef ).
Focus 2. {
symmetry.
unfold splice_into_list.
change (Z.to_nat 0) with 0. 
rewrite !Z.add_0_l, !Z.sub_0_r, !app_nil_l.
rewrite skipn_list_repeat by MyOmega.
rewrite (firstn_same _ (Z.to_nat (64 - _))) by MyOmega.
rewrite firstn_app1 by MyOmega.
reflexivity.
} Unfocus.
 unfold data_block.  rewrite prop_true_andp by auto.
 apply exp_right with (S256abs (hashed++blocks) dd').
 unfold sha256state_.
 entailer.
 apply exp_right with 
              (map Vint (hash_blocks init_registers (hashed ++ blocks)),
                (Vint (lo_part (bitlength hashed dd + len * 8)),
                 (Vint (hi_part (bitlength hashed dd + len * 8)),
                  (map Vint (map Int.repr dd'), Vint (Int.repr (Zlength dd')))))).
 unfold s256_relate, s256_h, s256_Nh, s256_Nl, s256_data, s256_num.
 simpl @fst; simpl @snd.
assert (bitlength hashed dd + len * 8 =
            bitlength (hashed ++ blocks) dd')%Z. {
    unfold bitlength, dd'. rewrite (Zlength_correct (firstn _ _)).
    rewrite Zlength_app.
    rewrite firstn_length.
    rewrite skipn_length by omega.
    rewrite min_l
    by (apply Nat2Z.inj_le; 
         rewrite Nat2Z.inj_sub; 
         [ repeat rewrite Z2Nat.id by omega;
          rewrite <- Zlength_correct; omega
         | apply Nat2Z.inj_le; 
          repeat rewrite Z2Nat.id by omega;
          rewrite <- Zlength_correct; omega
         ]).  
    rewrite Z2Nat.id by omega.
    unfold b4d.
    rewrite <- !Z.mul_add_distr_r.
    change (Z.of_nat 4) with WORD.
    change 4%Z with WORD.
    rewrite (Z.mul_add_distr_r _ _ WORD).
    omega.        
}
 rewrite H6.
 entailer!.
 -
 apply Update_abs; auto.
 omega.
 rewrite Hblocks.
 repeat rewrite app_ass.
 f_equal.
 unfold dd'.
 replace (length blocks * 4 - length dd) with (Z.to_nat b4d).
 rewrite firstn_app.
 f_equal.
 rewrite <- Z2Nat.inj_add by omega. f_equal. omega.
 apply Nat2Z.inj.
 rewrite Nat2Z.inj_sub, Nat2Z.inj_mul. MyOmega.
  apply Nat2Z.inj_le.
  rewrite Nat2Z.inj_mul.
  MyOmega.
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
 rename H0 into H2'.
 rewrite H2'.
 entailer!.
 constructor; auto.
 rewrite <- app_nil_end.
 rewrite Hblocks. f_equal. f_equal.
clear - Hblocks_len H2' Hlen H3 H.
 apply Nat2Z.inj.
 rewrite ?Nat2Z.inj_sub, ?Nat2Z.inj_add, ?Nat2Z.inj_mul.
MyOmega.
 apply Nat2Z.inj_le.
MyOmega.
 unfold sha256state_.
 set (bitlen := (bitlength hashed dd + len * 8)%Z). 
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
 replace len with (Zlength blocks * 4 - Zlength dd)%Z by (clear - H2'; omega).
 change 4%Z with WORD.
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
fold update_outer_if in *.
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
simpl in LEN, HBOUND.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd in H0|-*.
destruct H0 as [H0 [H1 [H8 [[H3 H3'] [H4 H5]]]]].
destruct H1 as [H1 H6].
subst.

unfold_data_at 1%nat.
forward_call' (* SHA256_addlength(c, len); *)
  (len, c, s256a_len (S256abs hashed dd)).
  repeat split; simpl; omega.
(* TODO:  need a fold_data_at tactic; the next few lines do that here *)
gather_SEP' [4;0;1;2;3]%Z;
match goal with |- context [SEPx (?A::_)] =>
 replace A with (`(data_at Tsh t_struct_SHA256state_st
    (map Vint (hash_blocks init_registers hashed),
        (Vint (lo_part (bitlength hashed dd + len * 8)),
        (Vint (hi_part (bitlength hashed dd + len * 8)),
        (map Vint (map Int.repr dd), Vint (Int.repr (Zlength dd)))))) c))
   by (unfold_data_at 1%nat; reflexivity)
end.
(* end of TODO *)

forward. (* n = c->num; *)
forward. (* p=c->data; *)
    (* TODO: should this produce field_address instead of (Int.repr 40) ? *)
assert_PROP (field_address t_struct_SHA256state_st [StructField _data] c
          = offset_val (Int.repr 40) c).
  unfold_data_at 1%nat; rewrite (field_at_compatible' _ _ [StructField _data]).
  entailer!. (* should field_at_compatible' be part of 
                       saturate_locals? *)
  apply field_address_clarify; auto.
rewrite <- H0; clear H0.
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
                    PROP  (update_abs (firstn (Z.to_nat len) data) (S256abs hashed dd) a')
                    LOCAL (gvar  _K256 kv)
                    SEP 
                    (`(K_vector kv);
                     `(sha256state_ a' c); `(data_block sh data d))).

make_sequential.
 semax_subcommand Vprog Gtot  f_SHA256_Update.
fold update_last_if.
rewrite <- data_at_offset_zero.
simpl upd_reptype.
pose proof (Hblocks_lem H2).
replace (Z.of_nat (length blocks * 4 - length dd))
    with (Zlength blocks * 4 - Zlength dd)%Z.
simple apply update_last_if_proof; try assumption; try omega.
apply Nat2Z.inj_ge in H6.
rewrite Nat2Z.inj_mul, <- !Zlength_correct in H6. change (Z.of_nat 4) with 4%Z in H6.
 omega.
 rewrite Nat2Z.inj_sub by auto. 
 rewrite Nat2Z.inj_mul, <- !Zlength_correct.
 reflexivity.
abbreviate_semax.
(* after the last if *)
 apply extract_exists_pre; intro a'.
 forward.  (* return; *)
 apply exp_right with a'.
 entailer!.
Qed.
