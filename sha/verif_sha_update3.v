Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.verif_sha_update2.
Local Open Scope nat.
Local Open Scope logic.

Lemma map_firstn: forall A B (f: A -> B) len data,
    map f (firstn len data) = firstn len (map f data).
Proof.
induction len; destruct data; simpl; auto.
f_equal; auto.
Qed.

Lemma update_inner_if_else_proof:
 forall (Espec : OracleKind) (hashed : list int)
          (dd data : list Z) (c d: val) (sh: share) (len: nat)
          (hi lo: int) Post
   (H : (Z.of_nat len <= Zlength data)%Z)
   (H7 : ((Zlength hashed * 4 + Zlength dd) * 8)%Z = hilo hi lo)
   (H3 : (Zlength dd < CBLOCKz)%Z)
   (H3' : Forall isbyteZ dd)
   (H4 : (LBLOCKz | Zlength hashed))
   (Hlen : (Z.of_nat len <= Int.max_unsigned)%Z)
   (c' : name _c) (data_ : name _data) (len' : name _len) 
   (data' : name _data) (p : name _p) (n : name _n)
   (fragment_ : name _fragment),
  let j := (40 + Zlength dd)%Z in
  let k := (64 - Zlength dd)%Z in
  forall (H0: (0 < k <= 64)%Z)
       (H1: (64 < Int.max_unsigned)%Z)
       (DBYTES: Forall isbyteZ data),
 semax Delta_update_inner_if
  (PROP  ()
   LOCAL 
   (`(typed_false tint)
      (eval_expr
         (Ebinop Oge (Etempvar _len tuint) (Etempvar _fragment tuint) tint));
   `(eq (Vint (Int.repr k))) (eval_id _fragment);
   `(eq (offset_val (Int.repr 40) c)) (eval_id _p);
   `(eq (Vint (Int.repr (Zlength dd)))) (eval_id _n); `(eq c) (eval_id _c);
   `(eq d) (eval_id _data);
   `(eq (Vint (Int.repr (Z.of_nat len)))) (eval_id _len))
   SEP 
   (`(array_at tuint Tsh (tuints (hash_blocks init_registers hashed)) 0 8 c);
   `(sha256_length (hilo hi lo + Z.of_nat len * 8) c);
   `(array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd))) 0 64
       (offset_val (Int.repr 40) c));
   `(field_at Tsh t_struct_SHA256state_st [_num] (Vint (Int.repr (Zlength dd)))
       c); `K_vector (eval_var _K256 (tarray tuint 64));
   `(array_at tuchar sh (tuchars (map Int.repr data)) 0 (Zlength data) d)))
  update_inner_if_else
  (overridePost Post
     (function_body_ret_assert tvoid
        (EX  a' : s256abs,
         PROP  (update_abs (firstn len data) (S256abs hashed dd) a')
         LOCAL ()
         SEP  (`K_vector (eval_var _K256 (tarray tuint 64));
                 `(sha256state_ a' c); `(data_block sh data d))))).
Proof.
  intros.
  unfold update_inner_if_else;
  simplify_Delta; abbreviate_semax;
  forward_call (* memcpy (p+n, data, len); *)
      ((sh,Tsh), 
       offset_val (Int.repr (Zlength dd)) (offset_val (Int.repr 40) c),
       d, 
       Z.of_nat len,
       Basics.compose force_int (ZnthV tuchar (map Vint (map Int.repr data)))).
  (* prove the entailment for call *)
  simpl @snd.
  normalize.
  fold j; fold k.
  entailer!.
  rewrite cVint_force_int_ZnthV
  by (rewrite initial_world.Zlength_map; omega).
  rewrite negb_false_iff in H5.
  apply ltu_repr in H5; [ | repable_signed | omega].
  unfold j,k in *; clear j k.
  replace (offset_val (Int.repr (40 + Zlength dd)) c)
           with (offset_val (Int.repr (sizeof tuchar * Zlength dd)) (offset_val (Int.repr 40) c))
   by (change (sizeof tuchar) with 1%Z; rewrite Z.mul_1_l; rewrite offset_offset_val, add_repr; auto).

  rewrite memory_block_array_tuchar';  [ | destruct c; try contradiction Pc; apply I | omega].
  unfold tuchars.
  rewrite (split_array_at (Zlength dd + Z.of_nat len) _ _ (ZnthV tuchar (map Vint (map Int.repr dd))))
    by omega.
  rewrite split_offset_array_at with (lo := Zlength dd) (contents := 
    ZnthV tuchar (map Vint (map Int.repr dd))); [| omega | simpl; omega | reflexivity].
  rewrite (split_array_at (Z.of_nat len) _ _ (tuchars (map Int.repr data)))
    by omega.
  replace (Zlength dd + Z.of_nat len - Zlength dd)%Z with (Z.of_nat len) by omega.
  unfold tuchars.
  cancel.

  (* manually do after_call *)
  cbv beta iota.
  autorewrite with norm subst.
  replace_SEP 0%Z 
  (`(array_at tuchar sh
          (cVint (force_int oo ZnthV tuchar (map Vint (map Int.repr data))))
          0 (Z.of_nat len) d *
        array_at tuchar Tsh
          (cVint (force_int oo ZnthV tuchar (map Vint (map Int.repr data))))
          0 (Z.of_nat len) (offset_val (Int.repr (40 + Zlength dd)) c))).
  entailer!.

  forward. (* c->num = n+(unsigned int)len; *)
  fold j; fold k.
  forward. (* return; *)
  rename H6 into H6'; rename H8 into H6.
  apply exp_right with (S256abs hashed (dd ++ firstn len data)).
  unfold id.
  unfold data_block.
  (* unfold K_vector. *)
  repeat rewrite TT_andp.
  rewrite cVint_force_int_ZnthV by (rewrite initial_world.Zlength_map; omega).
  rewrite array_at_tuchar_isbyteZ. 
  rewrite (prop_true_andp (Forall _ data)) by auto.
  rewrite negb_false_iff in H5.
  apply ltu_repr in H5; [ | repable_signed | omega].
  clear TC1.
  unfold k in H0,H5.
  rewrite (prop_true_andp (_ /\ _)).
  Focus 2. {
    split; auto.
    rewrite (app_nil_end hashed) at 2.
    apply (Update_abs _ hashed nil dd (dd++firstn len data)); auto.
    change CBLOCKz with (Z.of_nat CBLOCK).
    rewrite Zlength_correct. apply Nat2Z.inj_lt.
    rewrite app_length. rewrite firstn_length. rewrite min_l.
    apply Nat2Z.inj_lt. rewrite Nat2Z.inj_add.
    rewrite <- Zlength_correct. change (Z.of_nat CBLOCK) with 64%Z.
    omega.
    apply Nat2Z.inj_le; rewrite <- Zlength_correct; assumption.
    exists 0%Z. reflexivity.
  } Unfocus.
  unfold sha256state_.
  normalize. (* clear H8. *)
  unfold sha256_length,  tuchars, tuints.
  normalize. rename x0 into hi'; rename x into lo'.
  apply exp_right with
     (map Vint (hash_blocks init_registers hashed),
     (Vint lo',
     (Vint hi',
     (map Vint (map Int.repr (dd ++ firstn len data)),
     (Vint (Int.repr (Zlength dd + Z.of_nat len))))))).
  rewrite prop_true_andp.
  + unfold_data_at 1%nat.
    unfold_field_at 4%nat.
    unfold_field_at 6%nat.
    erewrite (add_andp (field_at Tsh t_struct_SHA256state_st [_num]
       (Vint (Int.repr (Zlength dd + Z.of_nat len))) c'));
       [| rewrite field_at_data_at by reflexivity;
       apply andp_left1, andp_left1, derives_refl].   
       (* This step is to remove right side local facts, which is provable. *)
    normalize.
    cancel.
    pull_left (array_at tuchar sh (ZnthV tuchar (map Vint (map Int.repr data)))
     (Z.of_nat len) (Zlength data) data').
    pull_left (array_at tuchar sh (ZnthV tuchar (map Vint (map Int.repr data))) 0
     (Z.of_nat len) data').
    rewrite <- split_array_at by omega.
    replace (offset_val (Int.repr j) c')
      with (offset_val (Int.repr (sizeof tuchar * Zlength dd)) (offset_val (Int.repr 40) c')).
    Focus 2. {
      change (sizeof tuchar) with 1%Z; rewrite Z.mul_1_l.
      unfold j. rewrite offset_offset_val. rewrite add_repr; auto.
    } Unfocus.
    cancel.
    rewrite (split_array_at (Zlength dd+ Z.of_nat len) _ _ _ 0 64) by omega.
    rewrite split_offset_array_at with (lo := Zlength dd) (hi := (Zlength dd + Z.of_nat len)%Z); 
        [| omega| simpl; omega | reflexivity].
    pull_left (array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd))) 0
      (Zlength dd) (offset_val (Int.repr 40) c')).
    normalize.
  
    replace (Zlength dd + Z.of_nat len - Zlength dd)%Z with (Z.of_nat len) by omega.
    repeat rewrite <- sepcon_assoc.
    repeat apply sepcon_derives; apply derives_refl'; apply equal_f;
    apply array_at_ext; intros.
    - unfold ZnthV. repeat rewrite if_false by omega.
      repeat rewrite map_map. 
      repeat rewrite (@nth_map' Z val _ _ 0%Z).
      f_equal. f_equal.
      rewrite app_nth1; auto. 
      apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega.
      rewrite <- Zlength_correct; apply H12.
      rewrite app_length.
      apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega.
      rewrite firstn_length.
      rewrite min_l.
      rewrite Nat2Z.inj_add.
       rewrite <- Zlength_correct.
      omega.
      apply Nat2Z.inj_le. rewrite <- Zlength_correct; assumption.
      apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega.
      rewrite <- Zlength_correct; apply H12.
    - unfold cVint, force_int, Basics.compose.
      unfold ZnthV.
      rewrite if_false by omega.
      rewrite if_false by omega.
      repeat rewrite map_map.
      rewrite map_app.
      rewrite app_nth2; auto.
      rewrite map_firstn, nth_firstn_low.
      rewrite map_length.
      assert (Z.to_nat i < length data). {
        apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega.
        rewrite <- Zlength_correct. omega.
      }
      replace (Z.to_nat (i + Zlength dd) - length dd) with (Z.to_nat i).
      Focus 1. { repeat rewrite (@nth_map' Z val _ _ 0%Z) by auto. auto. } Unfocus.
      rewrite Z2Nat.inj_add.
      assert (Z.to_nat (Zlength dd) = length dd).
        rewrite Zlength_correct.
        apply Nat2Z.id.
      omega.
      omega.
      rewrite Zlength_correct.
      omega.
      rewrite map_length. rewrite map_length.
      split.
      apply Nat2Z.inj_lt. rewrite Nat2Z.inj_sub.
      rewrite Z2Nat.id by omega.
      rewrite <- Zlength_correct; omega.
      apply Nat2Z.inj_le. 
      rewrite <- Zlength_correct; rewrite Z2Nat.id by omega. omega. 
      apply Nat2Z.inj_le.
      rewrite <- Zlength_correct; omega.
      rewrite map_length.
      apply Nat2Z.inj_ge. 
      rewrite <- Zlength_correct; rewrite Z2Nat.id by omega;  omega.
    - unfold ZnthV.
      repeat rewrite if_false by omega.
      repeat rewrite map_map. rewrite map_app.
      rewrite nth_overflow. rewrite nth_overflow. auto.
      rewrite app_length, map_length, map_length.
      rewrite firstn_length. rewrite min_l.
      apply Nat2Z.inj_ge. rewrite Nat2Z.inj_add.
      rewrite <- Zlength_correct; rewrite Z2Nat.id by omega;  omega.
      apply Nat2Z.inj_ge.
      rewrite <- Zlength_correct; omega.
      rewrite map_length.
      apply Nat2Z.inj_le. rewrite Z2Nat.id by omega; 
      rewrite <- Zlength_correct; omega.
  + repeat split.
    exists hi', lo'. simpl. repeat split; auto.
    rewrite H9.
    rewrite <- H7.
    rewrite <- Z.mul_add_distr_r.
    f_equal.
    rewrite <- Z.add_assoc.
    f_equal. rewrite initial_world.Zlength_app; f_equal.
    rewrite Zlength_correct; f_equal.
    rewrite firstn_length; apply min_l.
    apply Nat2Z.inj_ge.
    rewrite <- Zlength_correct; omega.
    change CBLOCKz with (Z.of_nat CBLOCK).
    rewrite Zlength_correct. apply Nat2Z.inj_lt.
    rewrite app_length.
    rewrite firstn_length, min_l.
    apply Nat2Z.inj_lt. 
    rewrite Nat2Z.inj_add.
    rewrite <- Zlength_correct; change (Z.of_nat CBLOCK) with 64%Z; omega.
    apply Nat2Z.inj_le.
    rewrite <- Zlength_correct; omega.
    rewrite Forall_app; split; auto.
    apply Forall_firstn; auto.
    auto.
    unfold s256_num.
    simpl.
    do 2 f_equal.
    rewrite initial_world.Zlength_app; f_equal.
    rewrite Zlength_correct; f_equal.
    symmetry;
    rewrite firstn_length; apply min_l.
    apply Nat2Z.inj_ge.
    rewrite <- Zlength_correct; omega.
Qed.

Lemma update_inner_if_proof:
 forall (Espec: OracleKind) (hashed: list int) (dd data: list Z)
            (c d: val) (sh: share) (len: nat) (hi lo: int)
 (H: len <= length data)
 (H7 : ((Zlength hashed * 4 + Zlength dd) * 8)%Z = hilo hi lo)
 (H3 : (Zlength dd < CBLOCKz)%Z)
 (H3' : Forall isbyteZ dd)
 (H4 : (LBLOCKz | Zlength hashed))
 (Hlen : (Z.of_nat len <= Int.max_unsigned)%Z),
semax Delta_update_inner_if
  (inv_at_inner_if sh hashed len c d dd data hi lo)
  update_inner_if
  (overridePost (sha_update_inv sh hashed len c d dd data hi lo false)
     (function_body_ret_assert tvoid
        (EX  a' : s256abs,
         PROP  (update_abs (firstn len data) (S256abs hashed dd) a')
         LOCAL ()
         SEP  (`K_vector (eval_var _K256 (tarray tuint 64));
                 `(sha256state_ a' c); `(data_block sh data d))))).
Proof.
intros.
name c' _c.
name data_ _data_.
name len' _len.
name data' _data.
name p _p.
name n _n.
name fragment_ _fragment.
simplify_Delta.
unfold sha_update_inv, inv_at_inner_if, update_inner_if.
abbreviate_semax.
rewrite semax_seq_skip.
 set (j := (40 + Zlength dd)%Z).
 set (k := (64-Zlength dd)%Z).
assert (0 < k <= 64)%Z.
 unfold k; clear - H3; change CBLOCKz with 64%Z in H3.
 assert (0 <= Zlength dd)%Z by (rewrite Zlength_correct; clear; omega).
 omega.
 assert (64 < Int.max_unsigned)%Z
  by (compute; reflexivity).
apply Nat2Z.inj_le in H; rewrite <- Zlength_correct in H.
unfold data_block; simpl. normalize.
rename H2 into DBYTES.
forward_if (sha_update_inv sh hashed len c d dd data hi lo false).
 + replace Delta with (initialized _fragment (initialized _p (initialized _n (initialized _data
                     (func_tycontext f_SHA256_Update Vprog Gtot)))))
 by (simplify_Delta; reflexivity).
 simpl typeof.
 unfold POSTCONDITION, abbreviate.
 rewrite overridePost_overridePost.
 unfold k. 
 simple eapply update_inner_if_then_proof; try eassumption.
 + (* else clause: len < fragment *)
 replace Delta with (initialized _fragment (initialized _p (initialized _n (initialized _data
                     (func_tycontext f_SHA256_Update Vprog Gtot)))))
 by (simplify_Delta; reflexivity).
 simpl typeof.
 unfold POSTCONDITION, abbreviate.
 rewrite overridePost_overridePost. 
 eapply update_inner_if_else_proof; eassumption.
 + forward. (* bogus skip *)
    rewrite overridePost_normal'.
    apply andp_left2; auto.
Qed.
