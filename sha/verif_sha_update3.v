Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.call_memcpy.
Require Import sha.verif_sha_update2.
Local Open Scope nat.
Local Open Scope logic.


Lemma firstn_app2: forall {A} n (p l: list A), (* duplicate *)
  (n > Datatypes.length p)%nat ->
   firstn n (p ++ l) = p ++ (firstn (n-Datatypes.length p) l).
Proof. intros A n.
induction n; simpl; intros. 
  destruct p; simpl in *. trivial. omega.
  destruct p; simpl in *. trivial.
  rewrite IHn. trivial. omega. 
Qed.  

Lemma skipn_list_repeat:
   forall A k n (a: A),
     (k <= n)%nat -> 
     skipn k (list_repeat n a) = list_repeat (n-k) a.
Proof.
 induction k; destruct n; simpl; intros; auto.
 apply IHk; auto. omega.
Qed.

Lemma update_inner_if_else_proof:
 forall (Espec : OracleKind) (hashed : list int)
          (dd data : list Z) (c d: val) (sh: share) (len: Z) kv
          Post
   (H : (0 <= len <= Zlength data)%Z)
   (LEN64: (bitlength hashed dd  + len * 8 < two_p 64)%Z)
   (H3 : (Zlength dd < CBLOCKz)%Z)
   (H3' : Forall isbyteZ dd)
   (H4 : (LBLOCKz | Zlength hashed))
   (Hlen : (len <= Int.max_unsigned)%Z)
   (c' : name _c) (data_ : name _data) (len' : name _len) 
   (data' : name _data) (p : name _p) (n : name _n)
   (fragment_ : name _fragment),
  let k := (64 - Zlength dd)%Z in
  forall (H0: (0 < k <= 64)%Z)
       (H1: (64 < Int.max_unsigned)%Z)
       (H2 : (len < k)%Z)
       (DBYTES: Forall isbyteZ data),
 semax Delta_update_inner_if
  (PROP  ()
   LOCAL 
   (temp _fragment (Vint (Int.repr k)); 
     temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
     temp _n (Vint (Int.repr (Zlength dd)));
     temp _c c; temp _data d;
     temp _len (Vint (Int.repr (len)));
     gvar _K256 kv)
   SEP (`(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + (len)*8)),
                   (Vint (hi_part (bitlength hashed dd + (len)*8)),
                    (map Vint (map Int.repr dd),
                     Vint (Int.repr (Zlength dd))))))
               c);
         `(K_vector kv);
         `(data_at sh (tarray tuchar (Zlength data)) (map Vint (map Int.repr data)) d)))
  update_inner_if_else
  (overridePost Post
     (function_body_ret_assert tvoid
        (EX  a' : s256abs,
         PROP  (update_abs (firstn (Z.to_nat len) data) (S256abs hashed dd) a')
         LOCAL ()
         SEP  (`(K_vector kv);
                 `(sha256state_ a' c); `(data_block sh data d))))).
Proof.
  intros.
  unfold update_inner_if_else;
  simplify_Delta; abbreviate_semax.

 assert_PROP (field_address (tarray tuchar (Zlength data)) [ArraySubsc 0] d = d). {
  entailer.
  rewrite (data_at_field_at sh  (tarray tuchar (Zlength data))).
    rewrite (field_at_compatible' sh).
    entailer!.
    unfold field_address; rewrite if_true.
    unfold nested_field_offset2; simpl. normalize.
    admit.  (* field_compatible_cons *)
  }
 rename H5 into Hd.
 eapply semax_seq'.
 evar (Frame: list (LiftEnviron mpred)).
  eapply(call_memcpy_tuchar
   (*dst*) Tsh t_struct_SHA256state_st [StructField _data] (Zlength dd) (map Vint (map Int.repr dd)) c
   (*src*) sh (tarray tuchar (Zlength data)) [ ] 0 (map Int.repr data)  d
   (*len*) (len)
        Frame);
   try reflexivity; auto; try omega.
  apply Zlength_nonneg.
  repeat rewrite Zlength_map; unfold k in *; omega.
  clear - H0 H2; unfold k in *; omega.
  rewrite Zlength_map; clear - H H0 H2; unfold k in *; omega.
 rewrite (data_at_field_at sh).
 unfold_data_at 1%nat.
 entailer!.

auto.
 rewrite field_address_clarify; auto.
 normalize.
 rewrite field_address_clarify; auto.
 normalize.
 f_equal.
 erewrite nested_field_offset2_Tarray; try reflexivity.
 normalize. 
 unfold field_address in TC; destruct c; try contradiction;
  if_tac in TC; try contradiction.
 unfold field_address; rewrite if_true; auto.
 clear - H7 H0; unfold k in *.
 admit.  (* field_compatible_cons *)

rewrite (field_at_data_equal Tsh t_struct_SHA256state_st [StructField _data] 
                 _ (map Vint (map Int.repr dd)++ firstn (Z.to_nat len) (map Vint (map Int.repr data)))).
Focus 2. {
 assert (Z.to_nat (Zlength dd) = length (map Vint (map Int.repr dd)))
   by MyOmega.
 unfold splice_into_list.
 rewrite firstn_app1 by omega.
 rewrite firstn_same by omega.
 replace (Zlength dd + len - Zlength dd)%Z with (len) by omega.
 rewrite !Zlength_map.
 simpl skipn at 1.
 rewrite firstn_app1 by MyOmega.
 rewrite <- skipn_firstn.
 replace (Z.to_nat (Zlength dd + len) +
         Z.to_nat (64 - (Zlength dd + len)))
   with 64 by Omega1.
  rewrite firstn_app2 by MyOmega.
  rewrite (firstn_same _ (64 - _)%nat)
    by (rewrite length_list_repeat, !map_length, Zlength_correct, Z2Nat.inj_sub; Omega1).
  rewrite skipn_app2 by MyOmega.
  rewrite !map_length.
  replace (Z.to_nat (Zlength dd + len) - length dd) 
    with (Z.to_nat len) by Omega1.
 rewrite skipn_list_repeat by Omega1.
 rewrite <- app_ass.
 apply data_equal_sym.
 apply data_equal_list_repeat_default.
} Unfocus.

apply semax_pre with
  (PROP  ()
   LOCAL  (temp _fragment (Vint (Int.repr k));
   temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
   temp _n (Vint (Int.repr (Zlength dd))); temp _c c; temp _data d;
   temp _len (Vint (Int.repr (len)));
   gvar _K256 kv)
   SEP 
   (`(data_at Tsh t_struct_SHA256state_st
         (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + len*8)),
                   (Vint (hi_part (bitlength hashed dd + len*8)),
                    (map Vint (map Int.repr (dd ++ firstn (Z.to_nat len) data)),
                     Vint (Int.repr (Zlength dd))))))
               c);
   `(field_at sh (tarray tuchar (Zlength data)) []
       (map Vint (map Int.repr data)) d);
     `(K_vector kv))). {
  unfold_data_at 1%nat.
  entailer!.
  repeat rewrite firstn_map. repeat rewrite <- map_app.
 apply derives_refl.
}
  abbreviate_semax.
  forward. (* c->num = n+(unsigned int)len; *)
  forward. (* return; *)
  apply exp_right with (S256abs hashed (dd ++ firstn (Z.to_nat len) data)).
  repeat rewrite TT_andp.
  unfold data_block.
  rewrite (prop_true_andp (Forall _ data)) by auto.
  subst k.
  rewrite (prop_true_andp (_ /\ _)).
  Focus 2. {
    split; auto.
    rewrite (app_nil_end hashed) at 2.
    apply (Update_abs _ hashed nil dd (dd++firstn (Z.to_nat len) data)); auto.
  rewrite Zlength_app, (Zlength_correct (firstn _ _)),
           firstn_length, min_l; Omega1.
   apply Z.divide_0_r.
  } Unfocus.
  unfold sha256state_.
  cancel.
 eapply exp_right; apply andp_right; [ | apply derives_refl].
 apply prop_right.
 simpl. unfold s256_Nh, s256_Nl, bitlength. simpl.
 rewrite <- Z.mul_add_distr_r, Zlength_app, Z.add_assoc,
     (Zlength_correct (firstn _ _)), firstn_length, min_l,
     Z2Nat.id; try omega.
 repeat split; auto; try Omega1.
*  rewrite Forall_app; split; auto.
    apply Forall_firstn; auto.
* Omega1. 
Qed.

Lemma update_inner_if_proof:
 forall (Espec: OracleKind) (hashed: list int) (dd data: list Z)
            (c d: val) (sh: share) (len: Z) kv
 (H: (0 <= len <= Zlength data)%Z)
 (LEN64: (bitlength hashed dd  + len * 8 < two_p 64)%Z)
 (H3 : (Zlength dd < CBLOCKz)%Z)
 (H3' : Forall isbyteZ dd)
 (H4 : (LBLOCKz | Zlength hashed))
 (Hlen : (len <= Int.max_unsigned)%Z),
semax Delta_update_inner_if
  (inv_at_inner_if sh hashed len c d dd data kv)
  update_inner_if
  (overridePost (sha_update_inv sh hashed len c d dd data kv false)
     (function_body_ret_assert tvoid
        (EX  a' : s256abs,
         PROP  (update_abs (firstn (Z.to_nat len) data) (S256abs hashed dd) a')
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
assert (0 < k <= 64)%Z by Omega1.
pose proof I.
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
 match goal with |- semax ?D _ _ _ =>
  change D with Delta_update_inner_if
 end.
 simple eapply update_inner_if_then_proof; try eassumption.
  omega. Omega1.
 + (* else clause: len < fragment *)
 replace Delta with (initialized _fragment (initialized _p (initialized _n (initialized _data
                     (func_tycontext f_SHA256_Update Vprog Gtot)))))
 by (simplify_Delta; reflexivity).
 simpl typeof.
 unfold POSTCONDITION, abbreviate.
 rewrite overridePost_overridePost. 
 eapply update_inner_if_else_proof; try assumption; Omega1.
 +
   forward. (* bogus skip *)
   apply andp_left2; auto.
Qed.
