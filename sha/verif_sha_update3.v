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
   (Hsh: readable_share sh)
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
     temp _data d; temp _c c; 
     temp _len (Vint (Int.repr (len)));
     gvar _K256 kv)
   SEP (`(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + (len)*8)),
                   (Vint (hi_part (bitlength hashed dd + (len)*8)),
                    (map Vint (map Int.repr dd) ++ list_repeat (Z.to_nat (CBLOCKz-Zlength dd)) Vundef,
                     Vint (Int.repr (Zlength dd))))))
               c);
         `(K_vector kv);
         `(data_at sh (tarray tuchar (Zlength data)) (map Vint (map Int.repr data)) d)))
  update_inner_if_else
  (overridePost Post
     (function_body_ret_assert tvoid
        (EX  a' : s256abs,
         PROP  (update_abs (sublist 0 len data) (S256abs hashed dd) a')
         LOCAL ()
         SEP  (`(K_vector kv);
                 `(sha256state_ a' c); `(data_block sh data d))))).
Proof.
  intros.
  unfold update_inner_if_else;
  simplify_Delta; abbreviate_semax.

 assert_PROP (field_address0 (tarray tuchar (Zlength data)) [ArraySubsc 0] d = d). {
  entailer!.
  unfold field_address0. rewrite if_true. 
  normalize. eapply field_compatible0_cons_Tarray; try reflexivity; auto.
  Omega1.
}
 rename H5 into Hd.
 eapply semax_seq'.
 evar (Frame: list (LiftEnviron mpred)).
  eapply(call_memcpy_tuchar
   (*dst*) Tsh t_struct_SHA256state_st [StructField _data] (Zlength dd)
                     (map Vint (map Int.repr dd) ++
         list_repeat (Z.to_nat (CBLOCKz - Zlength dd)) Vundef) c
   (*src*) sh (tarray tuchar (Zlength data)) [ ] 0 (map Int.repr data)  d
   (*len*) (len)
        Frame);
   try reflexivity; auto; try omega.
  apply Zlength_nonneg.
  repeat rewrite Zlength_map; unfold k in *; omega.
 entailer!.
 unfold field_address, field_address0.
 rewrite !if_true; auto.
 erewrite nested_field_offset2_ind.
 normalize. f_equal. f_equal. f_equal. unfold gfield_offset; simpl. 
 clear; omega.
 apply compute_legal_nested_field0_spec'.
 repeat constructor; auto; try Omega1.
 apply field_compatible0_cons; simpl. split; auto; Omega1.
 unfold data_at.
 unfold_field_at 1%nat. cancel.
 abbreviate_semax.
 autorewrite with sublist.
 unfold splice_into_list. 
 assert (H5: (0 <= Zlength dd < 64)%Z) by (Omega1).
 assert (H6: (k = 64 - Zlength dd)%Z) by (unfold k; auto).
 autorewrite with sublist.
 change 64%Z with CBLOCKz.
 replace (CBLOCKz - (Zlength dd + (CBLOCKz - Zlength dd)))%Z
   with 0%Z by (clear; omega).
  change (list_repeat (Z.to_nat 0) Vundef) with (@nil val).
  rewrite <- app_nil_end.
  autorewrite with sublist.
  rewrite sublist_list_repeat by Omega1.
 clear H5 H6.
  forward. (* c->num = n+(unsigned int)len; *)
  forward. (* return; *)
  Exists (S256abs hashed (dd ++ sublist 0 len data)).
  repeat rewrite TT_andp.
  unfold data_block.
  rewrite (prop_true_andp (Forall _ data)) by auto.
  subst k.
  rewrite (prop_true_andp (_ /\ _)).
  Focus 2. {
    split; auto.
    rewrite (app_nil_end hashed) at 2.
    apply (Update_abs _ hashed nil dd (dd++sublist 0 len data)); auto.
    autorewrite with sublist; Omega1.
    apply Z.divide_0_r.
  } Unfocus.
  unfold sha256state_.
  cancel.
  Exists (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + len*8)),
                   (Vint (hi_part (bitlength hashed dd + len*8)),
                    (map Vint (map Int.repr (dd ++ sublist 0 len data))
                       ++list_repeat (Z.to_nat (64 - Zlength dd - len)) Vundef,
                     Vint (Int.repr (Zlength dd + len)))))).
 unfold data_at. unfold_field_at 6%nat.
 apply andp_right; [apply prop_right | ].
 simpl; unfold s256_Nh, s256_Nl, s256_data, s256_num, bitlength; simpl.
 autorewrite with sublist.
 rewrite !Z.mul_add_distr_r, !Z.add_assoc.
 repeat split; auto; try Omega1.
 rewrite Forall_app; split; auto; apply Forall_firstn; auto.
 cancel.
 repeat rewrite map_app. repeat rewrite <- sublist_map.
 rewrite <- app_assoc. auto.
Qed.

Lemma update_inner_if_proof:
 forall (Espec: OracleKind) (hashed: list int) (dd data: list Z)
            (c d: val) (sh: share) (len: Z) kv
 (H: (0 <= len <= Zlength data)%Z)
 (Hsh: readable_share sh)
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
         PROP  (update_abs (sublist 0 len data) (S256abs hashed dd) a')
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
unfold sha_update_inv, inv_at_inner_if, update_inner_if.
abbreviate_semax.
rewrite semax_seq_skip.
 set (k := (64-Zlength dd)%Z).
assert (0 < k <= 64)%Z by Omega1.
pose proof I.
unfold data_block; simpl. normalize.
rename H2 into DBYTES.
forward_if (sha_update_inv sh hashed len c d dd data kv false).
 +
  change Delta with Delta_update_inner_if.
 normalize_postcondition.
 unfold k.
 simple eapply update_inner_if_then_proof; try eassumption.
  omega. Omega1.
 + (* else clause: len < fragment *)
  change Delta with Delta_update_inner_if.
  weak_normalize_postcondition.
  unfold k.
  simple eapply update_inner_if_else_proof; try assumption; Omega1.
 +
   forward. (* bogus skip *)
   apply andp_left2; auto.
Qed.
