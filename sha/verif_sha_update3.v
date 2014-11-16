Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.verif_sha_update2.
Local Open Scope nat.
Local Open Scope logic.

Lemma update_inner_if_else_proof:
 forall (Espec : OracleKind) (hashed : list int)
          (dd data : list Z) (c d: val) (sh: share) (len: nat) kv
          Post
   (H : (Z.of_nat len <= Zlength data)%Z)
   (LEN64: (bitlength hashed dd  + Z.of_nat len * 8 < two_p 64)%Z)
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
       (DBYTES: Forall isbyteZ data),
 semax Delta_update_inner_if
  (PROP  ()
   LOCAL 
   (`(typed_false tint)
      (eval_expr
         (Ebinop Oge (Etempvar _len tuint) (Etempvar _fragment tuint) tint));
     temp _fragment (Vint (Int.repr k)); 
     temp _p (offset_val (Int.repr 40) c);
     temp _n (Vint (Int.repr (Zlength dd)));
     temp _c c; temp _data d;
     temp _len (Vint (Int.repr (Z.of_nat len)));
     var _K256 (tarray tuint CBLOCKz) kv)
   SEP (`(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + (Z.of_nat len)*8)),
                   (Vint (hi_part (bitlength hashed dd + (Z.of_nat len)*8)),
                    (map Vint (map Int.repr dd),
                     Vint (Int.repr (Zlength dd))))))
               c);
         `(K_vector kv);
         `(data_at sh (tarray tuchar (Zlength data)) (map Vint (map Int.repr data)) d)))
  update_inner_if_else
  (overridePost Post
     (function_body_ret_assert tvoid
        (EX  a' : s256abs,
         PROP  (update_abs (firstn len data) (S256abs hashed dd) a')
         LOCAL ()
         SEP  (`(K_vector kv);
                 `(sha256state_ a' c); `(data_block sh data d))))).
Proof.
  intros.
  unfold update_inner_if_else;
  simplify_Delta; abbreviate_semax.

(* get rid of typed_false *)
assert_PROP (Z.of_nat len < k)%Z. {
  entailer!.
  rewrite negb_false_iff in H5;
  apply ltu_repr in H5; [auto | repable_signed | omega].
}
drop_LOCAL 0.

 eapply semax_seq'.
 evar (Frame: list (LiftEnviron mpred)).
  eapply(call_memcpy_tuchar
   (*dst*) Tsh t_struct_SHA256state_st [StructField _data] (Zlength dd) (map Vint (map Int.repr dd)) c
   (*src*) sh (tarray tuchar (Zlength data)) [ ] 0 (map Int.repr data)  d
   (*len*) (Z.of_nat len)
        Frame);
   [ auto | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ].
 rewrite (data_at_field_at sh).
 unfold_data_at 1%nat.
 entailer!.
abbreviate_semax.
repeat rewrite firstn_map. repeat rewrite <- map_app.
rewrite skipn_0.
rewrite splice_into_list_simplify2
  by (repeat rewrite Zlength_map; omega).
rewrite Z.add_sub_swap, Z.sub_diag, Z.add_0_l, Nat2Z.id.
repeat rewrite firstn_map, <- map_app.

apply semax_pre with
  (PROP  ()
   LOCAL  (temp _fragment (Vint (Int.repr k));
   temp _p (offset_val (Int.repr 40) c);
   temp _n (Vint (Int.repr (Zlength dd))); temp _c c; temp _data d;
   temp _len (Vint (Int.repr (Z.of_nat len)));
   var _K256 (tarray tuint CBLOCKz) kv)
   SEP 
   (`(data_at Tsh t_struct_SHA256state_st
         (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + (Z.of_nat len)*8)),
                   (Vint (hi_part (bitlength hashed dd + (Z.of_nat len)*8)),
                    (map Vint (map Int.repr (dd ++ firstn len data)),
                     Vint (Int.repr (Zlength dd))))))
               c);
   `(field_at sh (tarray tuchar (Zlength data)) []
       (map Vint (map Int.repr data)) d);
     `(K_vector kv))). {
  unfold_data_at 1%nat.
  entailer!.
}

  forward. (* c->num = n+(unsigned int)len; *)
  forward. (* return; *)
  apply exp_right with (S256abs hashed (dd ++ firstn len data)).
  repeat rewrite TT_andp.
  unfold data_block.
  rewrite (prop_true_andp (Forall _ data)) by auto.
  unfold k in *; clear k.
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
  cancel.
 eapply exp_right; apply andp_right; [ | apply derives_refl].
 apply prop_right.
 simpl. unfold s256_Nh, s256_Nl, bitlength. simpl.
 rewrite <- Z.mul_add_distr_r, Zlength_app, Z.add_assoc,
     (Zlength_correct (firstn _ _)), firstn_length;
   rewrite min_l by (apply Nat2Z.inj_le; rewrite <- Zlength_correct; auto).
 repeat split; auto.
*
    change CBLOCKz with 64%Z.
    clear - H2; omega.
*
    rewrite Forall_app; split; auto.
    apply Forall_firstn; auto.
Qed.

Lemma update_inner_if_proof:
 forall (Espec: OracleKind) (hashed: list int) (dd data: list Z)
            (c d: val) (sh: share) (len: nat) kv
 (H: len <= length data)
 (LEN64: (bitlength hashed dd  + Z.of_nat len * 8 < two_p 64)%Z)
 (H3 : (Zlength dd < CBLOCKz)%Z)
 (H3' : Forall isbyteZ dd)
 (H4 : (LBLOCKz | Zlength hashed))
 (Hlen : (Z.of_nat len <= Int.max_unsigned)%Z),
semax Delta_update_inner_if
  (inv_at_inner_if sh hashed len c d dd data kv)
  update_inner_if
  (overridePost (sha_update_inv sh hashed len c d dd data kv false)
     (function_body_ret_assert tvoid
        (EX  a' : s256abs,
         PROP  (update_abs (firstn len data) (S256abs hashed dd) a')
         LOCAL ()
         SEP  (`(K_vector kv);
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
forward_if (sha_update_inv sh hashed len c d dd data kv false).
 + replace Delta with (initialized _fragment (initialized _p (initialized _n (initialized _data
                     (func_tycontext f_SHA256_Update Vprog Gtot)))))
 by (simplify_Delta; reflexivity).
 simpl typeof.
 unfold POSTCONDITION, abbreviate.
 rewrite overridePost_overridePost.
 unfold k. 
 simple eapply update_inner_if_then_proof; eassumption.
 + (* else clause: len < fragment *)
 replace Delta with (initialized _fragment (initialized _p (initialized _n (initialized _data
                     (func_tycontext f_SHA256_Update Vprog Gtot)))))
 by (simplify_Delta; reflexivity).
 simpl typeof.
 unfold POSTCONDITION, abbreviate.
 rewrite overridePost_overridePost. 
 eapply update_inner_if_else_proof; assumption.
 + forward. (* bogus skip *)
    rewrite overridePost_normal'.
    apply andp_left2; auto.
Qed.
