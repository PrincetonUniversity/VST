Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import JMeq.
Require Import sha.call_memcpy.
Local Open Scope nat.
Local Open Scope logic.

Definition update_inner_if_then :=
  (Ssequence
      (Scall None
           (Evar _memcpy
              (Tfunction
                 (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                 (tptr tvoid) cc_default))
           [Ebinop Oadd (Etempvar _p (tptr tuchar)) (Etempvar _n tuint)
              (tptr tuchar); Etempvar _data (tptr tuchar);
           Etempvar _fragment tuint])
     (Ssequence
        (Scall None
           (Evar _sha256_block_data_order
              (Tfunction
                 (Tcons (tptr t_struct_SHA256state_st)
                    (Tcons (tptr tvoid) Tnil)) tvoid cc_default))
           [Etempvar _c (tptr t_struct_SHA256state_st);
           Etempvar _p (tptr tuchar)])
        (Ssequence
           (Sset _data
              (Ebinop Oadd (Etempvar _data (tptr tuchar))
                 (Etempvar _fragment tuint) (tptr tuchar)))
           (Ssequence
              (Sset _len
                 (Ebinop Osub (Etempvar _len tuint)
                    (Etempvar _fragment tuint) tuint))
                 (Scall None
                    (Evar _memset
                       (Tfunction
                          (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                          (tptr tvoid) cc_default))
                    [Etempvar _p (tptr tuchar); Econst_int (Int.repr 0) tint;
                    Ebinop Omul (Econst_int (Int.repr 16) tint)
                      (Econst_int (Int.repr 4) tint) tint]))))).

Definition  update_inner_if_else :=
                (Ssequence
                    (Scall None
                      (Evar _memcpy (Tfunction
                                      (Tcons (tptr tvoid)
                                        (Tcons (tptr tvoid)
                                          (Tcons tuint Tnil))) (tptr tvoid) cc_default))
                      ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                         (Etempvar _n tuint) (tptr tuchar)) ::
                       (Etempvar _data (tptr tuchar)) ::
                       (Etempvar _len tuint) :: nil))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                          t_struct_SHA256state_st) _num tuint)
                      (Ebinop Oadd (Etempvar _n tuint)
                        (Ecast (Etempvar _len tuint) tuint) tuint))
                    (Sreturn None))).

Definition update_inner_if :=
        Sifthenelse (Ebinop Oge (Etempvar _len tuint)
                             (Etempvar _fragment tuint) tint)
         update_inner_if_then
         update_inner_if_else.

Definition inv_at_inner_if sh hashed len c d dd data kv :=
 (PROP ()
   (LOCAL 
      (temp _fragment (Vint (Int.repr (64- Zlength dd)));
       temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
       temp _n (Vint (Int.repr (Zlength dd)));
       temp _c c; temp _data d;
       temp _len (Vint (Int.repr (Z.of_nat len)));
       gvar  _K256 kv)
   SEP  (`(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + (Z.of_nat len)*8)),
                   (Vint (hi_part (bitlength hashed dd + (Z.of_nat len)*8)),
                    (map Vint (map Int.repr dd),
                     Vint (Int.repr (Zlength dd))))))
               c);
   `(K_vector kv);
   `(data_block sh data d)))).

Definition sha_update_inv sh hashed len c d (dd: list Z) (data: list Z) kv (done: bool) :=
   (EX blocks:list int,
   PROP  (len >= length blocks*4 - length dd /\
              (LBLOCKz | Zlength blocks) /\ 
              intlist_to_Zlist blocks = dd ++ firstn (length blocks * 4 - length dd) data /\
             if done then len-(length blocks*4 - length dd) < CBLOCK else True)
   LOCAL  (temp _p (field_address t_struct_SHA256state_st [StructField _data]  c); temp _c c; 
                temp _data (offset_val (Int.repr (Z.of_nat (length blocks*4-length dd))) d);
                temp _len (Vint (Int.repr (Z.of_nat (len- (length blocks*4 - length dd)))));
                gvar  _K256 kv)
   SEP  (`(K_vector kv);
           `(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers (hashed++blocks)),
                  (Vint (lo_part (bitlength hashed dd + (Z.of_nat len)*8)),
                   (Vint (hi_part (bitlength hashed dd + (Z.of_nat len)*8)),
                    (nil, Vundef))))
                c);
   `(data_block sh data d))).

Definition Delta_update_inner_if : tycontext.
simplify_Delta_from
  (initialized _fragment
     (initialized _p
        (initialized _n
           (initialized _data (func_tycontext f_SHA256_Update Vprog Gtot))))).
Defined.

Lemma data_block_data_field:
 forall sh dd dd' c, 
  Forall isbyteZ dd ->
  (Zlength dd = CBLOCKz)%Z ->
  JMeq (map Vint (map Int.repr dd)) dd' ->
  data_block sh dd (field_address t_struct_SHA256state_st [StructField _data] c) =
  field_at sh t_struct_SHA256state_st [StructField _data] dd' c.
Proof.
intros.
unfold data_block.
erewrite field_at_data_at by reflexivity.
repeat rewrite prop_true_andp by auto.
apply equal_f.
apply data_at_type_changable; auto.
rewrite H0; reflexivity.
Qed.

Lemma field_at_cancel_undef_example:
  forall  d c, 
  field_at Tsh t_struct_SHA256state_st [StructField _data] d c |--
  field_at Tsh t_struct_SHA256state_st [StructField _data] (list_repeat 64 Vundef) c.
Proof.
  intros.
  apply field_at_stronger.
  apply stronger_array_ext.
  intros.
  unfold Znth.
  if_tac; [omega |].
  rewrite nth_list_repeat.
  intros sh p.
  apply data_at_data_at_.
Qed.

Lemma update_inner_if_then_proof:
 forall (Espec : OracleKind) (hashed : list int)
          (dd data : list Z) (c d: val) (sh: share) (len: nat) kv
   (H : (Z.of_nat len <= Zlength data)%Z)
   (H3 : (Zlength dd < CBLOCKz)%Z)
   (H3' : Forall isbyteZ dd)
   (H4 : (LBLOCKz | Zlength hashed))
   (Hlen : (Z.of_nat len <= Int.max_unsigned)%Z)
   (c' : name _c) (data_ : name _data) (len' : name _len) 
   (data' : name _data) (p : name _p) (n : name _n)
   (fragment_ : name _fragment),
  let k := (64 - Zlength dd)%Z in
  forall (H0: (0 < k <= 64)%Z)
       (H1: (64 < Int.max_unsigned)%Z)
       (H2: (Z.of_nat len >= k)%Z)
       (DBYTES: Forall isbyteZ data),
semax Delta_update_inner_if
  (PROP  ()
   LOCAL 
   (temp _fragment (Vint (Int.repr k));
    temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
    temp _n (Vint (Int.repr (Zlength dd)));
    temp _c c; temp _data d; temp _len (Vint (Int.repr (Z.of_nat len)));
    gvar  _K256 kv)
   SEP 
   (`(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + (Z.of_nat len)*8)),
                   (Vint (hi_part (bitlength hashed dd + (Z.of_nat len)*8)),
                    (map Vint (map Int.repr dd),
                     Vint (Int.repr (Zlength dd))))))
               c);
   `(K_vector kv);
   `(data_at sh (tarray tuchar (Zlength data)) (map Vint (map Int.repr data)) d)))
  update_inner_if_then
  (overridePost (sha_update_inv sh hashed len c d dd data kv false)
     (function_body_ret_assert tvoid
        (EX  a' : s256abs,
         PROP  (update_abs (firstn len data) (S256abs hashed dd) a')
         LOCAL ()
         SEP  (`(K_vector kv); `(sha256state_ a' c); `(data_block sh data d))))).
Proof.
 intros.
 simplify_Delta; abbreviate_semax.
  unfold update_inner_if_then.
  apply (remember_value (eval_id _fragment)); intro fragment.
assert_PROP (fragment = Vint (Int.repr k)).
  entailer!.
drop_LOCAL 0. subst fragment.
match goal with |- semax ?D (PROP() (LOCALx ?Q (SEPx _))) _ _ =>
 apply semax_seq'
 with (PROP() (LOCALx Q 
        (SEP (`(data_at Tsh t_struct_SHA256state_st 
                 (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + (Z.of_nat len)*8)),
                   (Vint (hi_part (bitlength hashed dd + (Z.of_nat len)*8)),
                    (map Vint (map Int.repr dd) ++
                      firstn (Z.to_nat k) (map Vint (map Int.repr data)),
                     Vint (Int.repr (Zlength dd))))))
               c);
      `(K_vector kv);
      `(data_at sh (tarray tuchar (Zlength data)) (map Vint (map Int.repr data)) d)))))
end;
 [ eapply semax_post_flipped' | ].
*
  assert_PROP (field_address (tarray tuchar (Zlength data)) [ArraySubsc 0] d = d). {
    entailer.
    rewrite (data_at_field_at sh  (tarray tuchar (Zlength data))).
    rewrite (field_at_compatible' sh).
    entailer!.
    unfold field_address; rewrite if_true.
    unfold nested_field_offset2; simpl. normalize.
  eapply field_compatible_cons_Tarray; try reflexivity; auto.
 omega.
  }
 rename H5 into Hd.
  evar (Frame: list (LiftEnviron mpred)).
  eapply(call_memcpy_tuchar
   (*dst*) Tsh t_struct_SHA256state_st [StructField _data] (Zlength dd) (map Vint (map Int.repr dd)) c
   (*src*) sh (tarray tuchar (Zlength data)) [ ] 0 (map Int.repr data)  d
   (*len*) k
        Frame);
  try reflexivity; auto; try omega.
  apply Zlength_nonneg. repeat rewrite Zlength_map. unfold k in *; omega.
  unfold k; omega.
  rewrite Zlength_map. omega.
  unfold_data_at 1%nat.
  entailer!.
  rewrite field_address_clarify; auto.
  normalize.
  erewrite nested_field_offset2_Tarray; try reflexivity. 
  rewrite sizeof_tuchar, Z.mul_1_l.
  unfold field_address in *.
  if_tac in TC; try contradiction. normalize.
  apply isptr_is_pointer_or_null.
  apply field_address_isptr; auto.
  eapply field_compatible_cons_Tarray; try reflexivity; auto.
  unfold k in *; omega.
*
  rewrite skipn_0.
  rewrite (data_at_field_at sh).
  replace (Zlength dd + k - Zlength dd)%Z with k by (clear; omega).
  unfold_data_at 1%nat.
  entailer!.
  replace (Zlength dd + k)%Z with 64%Z by (unfold k; omega).
  rewrite splice_into_list_simplify2; try (repeat rewrite Zlength_map; omega).
  fold k. apply derives_refl.
  unfold k in H0; omega.
  repeat rewrite Zlength_map.
  clear - H2 H0 H.
  unfold k in *; clear k. omega.
*
  abbreviate_semax.
  repeat rewrite firstn_map. repeat rewrite <- map_app.
  unfold_data_at 1%nat.
  rewrite <- (data_block_data_field _ (dd ++ firstn (Z.to_nat k) data));
 [
 | rewrite Forall_app; split; auto; apply Forall_firstn; auto
 | rewrite Zlength_app, (Zlength_correct (firstn _ _)),
   firstn_length, min_l;
   [ rewrite Z2Nat.id by omega; unfold k; change CBLOCKz with 64%Z; omega
   | apply Nat2Z.inj_le;
     rewrite Z2Nat.id; [rewrite <- Zlength_correct; omega | omega ]]
 | reflexivity
 ].
normalize.
 assert (length (dd ++ firstn (Z.to_nat k) data) = 64). {
  unfold k in *.
  rewrite app_length.
  rewrite firstn_length, min_l.
  apply Nat2Z.inj. rewrite Nat2Z.inj_add.
  rewrite Z2Nat.id.
  change (Z.of_nat 64) with 64%Z.
  rewrite <- Zlength_correct; omega.
  omega.
  apply Nat2Z.inj_le.  rewrite Z2Nat.id.
  rewrite <- Zlength_correct; omega.
  omega.
 }
 assert (length (Zlist_to_intlist (dd ++ firstn (Z.to_nat k) data)) = LBLOCK). {
  apply length_Zlist_to_intlist. assumption.
 }
 forward_call' (* sha256_block_data_order (c,p); *)
   (hashed, Zlist_to_intlist (dd++(firstn (Z.to_nat k) data)), c,
     (field_address t_struct_SHA256state_st [StructField _data] c),
      Tsh, kv). {
 entailer.
 unfold k in *|-.
 rewrite Zlist_to_intlist_to_Zlist.
 cancel.
 unfold k; rewrite H5;  exists LBLOCK; reflexivity.
 rewrite Forall_app; split; auto; apply Forall_firstn; auto.
}
 split; auto.
 rewrite Zlength_correct; rewrite H6; reflexivity.
 simpl map.
 rewrite Zlist_to_intlist_to_Zlist;
 [
 | rewrite app_length, firstn_length;
   rewrite min_l 
    by (apply Nat2Z.inj_le; rewrite Z2Nat.id by omega; 
     rewrite <- Zlength_correct; omega);
   exists LBLOCK; unfold k;
   apply Nat2Z.inj; transitivity 64%Z; [ | reflexivity];
   rewrite Nat2Z.inj_add; rewrite Z2Nat.id by (fold k; omega);
   rewrite <- Zlength_correct; omega
 |  rewrite Forall_app; split; auto; apply Forall_firstn; auto
].
 erewrite data_block_data_field;
   auto; 
 [
 | rewrite Forall_app; split; auto; apply Forall_firstn; auto
 | rewrite Zlength_app, (Zlength_correct (firstn _ _)),
   firstn_length, min_l;
   [ rewrite Z2Nat.id by omega; unfold k; change CBLOCKz with 64%Z; omega
   | apply Nat2Z.inj_le;
     rewrite Z2Nat.id; [rewrite <- Zlength_correct; omega | omega ]]
 ].
forward data_old. (* data  += fragment; *)
forward len_old. (* len -= fragment; *)
  normalize_postcondition.
eapply semax_post_flipped3.
evar (Frame: list (LiftEnviron mpred)).
  eapply(call_memset_tuchar
   (*dst*) Tsh t_struct_SHA256state_st [StructField _data] 0 
                (map Vint (map Int.repr (dd ++ firstn (Z.to_nat k) data))) c
   (*src*) Int.zero
   (*len*) 64
        Frame); try reflexivity; auto.
 rewrite !Zlength_map. rewrite Zlength_correct, H5. compute; split; congruence.
 entailer!.
 rewrite !field_address_clarify. reflexivity.
 (apply isptr_is_pointer_or_null; apply field_address_isptr; auto).
 (apply isptr_is_pointer_or_null; apply field_address_isptr; auto).
 clear - TC. unfold field_address in TC. if_tac in TC; try contradiction. clear TC.
 hnf in H; decompose [and] H; clear H.
 split; auto. split; auto. split; auto. split3; auto.
 inv H6.
 constructor; auto. split; auto. omega.
  
 apply exp_right with (Zlist_to_intlist (dd ++ firstn (Z.to_nat k) data)).
 assert (KK: k = Z.of_nat (LBLOCK * 4 - length dd)). {
 unfold k.
 rewrite Nat2Z.inj_sub. rewrite Zlength_correct; reflexivity.
 unfold k in H0. clear - H0.
 apply Nat2Z.inj_le.
 change (Z.of_nat (LBLOCK*4)) with 64%Z.
 rewrite <- Zlength_correct.
 omega.
}

 rewrite (Zlength_correct (Zlist_to_intlist _)).
 rewrite H6.
 rewrite Zlist_to_intlist_to_Zlist;
 [
 | rewrite app_length, firstn_length;
   rewrite min_l 
    by (apply Nat2Z.inj_le; rewrite Z2Nat.id by omega; rewrite <- Zlength_correct; omega);
   exists LBLOCK; unfold k;
   apply Nat2Z.inj; transitivity 64%Z; [ | reflexivity];
   rewrite Nat2Z.inj_add; rewrite Z2Nat.id by (fold k; omega);
   rewrite <- Zlength_correct; omega
 |  rewrite Forall_app; split; auto; apply Forall_firstn; auto
].

 simpl update_tycon; rewrite insert_local.
 rewrite splice_into_list_simplify0;
 [ 
 | rewrite Zlength_correct, length_list_repeat; reflexivity
 | rewrite Zlength_correct, map_length, map_length, H5; reflexivity].
unfold_data_at 2%nat.
change (Z.to_nat 64) with CBLOCK.
entailer!.
 +
  apply Nat2Z.inj_ge.
  rewrite Nat2Z.inj_sub.
  change (Z.of_nat (LBLOCK*4)) with 64%Z.
  rewrite <- Zlength_correct; omega.
  clear - H3. apply Nat2Z.inj_le. rewrite <- Zlength_correct.
  change (Z.of_nat (LBLOCK*4)%nat) with CBLOCKz; clear - H3; omega.
 + 
  f_equal. f_equal. rewrite Z2Nat.inj_sub by omega.
  rewrite Zlength_correct, Nat2Z.id.
  reflexivity.
 +
 rewrite <- KK. auto.
 +
 rewrite KK.
 rewrite Nat2Z.inj_sub; auto.
 apply Nat2Z.inj_le.
 rewrite Nat2Z.inj_sub.
 rewrite <- Zlength_correct.
 change (Z.of_nat (LBLOCK * 4)) with 64%Z.
 omega.
 apply Nat2Z.inj_le.
 rewrite <- Zlength_correct.
 change (Z.of_nat (LBLOCK * 4)) with 64%Z.
 omega.
 +
 unfold data_block; normalize.
Qed.
