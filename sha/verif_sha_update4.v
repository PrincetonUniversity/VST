Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.verif_sha_update2.
Require Import sha.verif_sha_update3.
Local Open Scope Z.
Local Open Scope logic.


Lemma Hblocks_lem:
 forall {blocks: list int} {frag: list Z} {data},
 intlist_to_Zlist blocks = frag ++ sublist 0 (Zlength blocks * 4 - Zlength frag) data ->
 Zlength frag <= Zlength blocks * 4.
Proof.
intros.
assert (Zlength (intlist_to_Zlist blocks) = 
               Zlength ( frag ++
     sublist 0 (Zlength blocks * 4 - Zlength frag) data)) by congruence.
 autorewrite with sublist in H0.
 pose proof (Zlength_nonneg (sublist 0 (Zlength blocks * 4 - Zlength frag) data)).
 omega.
Qed.

Definition sha_update_loop_body :=
  (Ssequence
     (Scall None
        (Evar _sha256_block_data_order
           (Tfunction
              (Tcons (tptr t_struct_SHA256state_st) (Tcons (tptr tvoid) Tnil))
              tvoid cc_default))
        [Etempvar _c (tptr t_struct_SHA256state_st);
        Etempvar _data (tptr tuchar)])
     (Ssequence
        (Sset _data
           (Ebinop Oadd (Etempvar _data (tptr tuchar))
              (Ebinop Omul (Econst_int (Int.repr 16) tint)
                 (Econst_int (Int.repr 4) tint) tint) (tptr tuchar)))
        (Sset _len
           (Ebinop Osub (Etempvar _len tuint)
              (Ebinop Omul (Econst_int (Int.repr 16) tint)
                 (Econst_int (Int.repr 4) tint) tint) tuint)))).


Lemma split2_data_block:
  forall n sh data d,
  (0 <= n <= Zlength data)%Z ->
  data_block sh data d = 
  (data_block sh (sublist 0 n data) d *
   data_block sh (sublist n (Zlength data) data) 
   (field_address0 (tarray tuchar (Zlength data)) [ArraySubsc n] d))%logic.
Proof.
intros.
unfold data_block. simpl.
normalize.
f_equal. 
*
f_equal.
apply prop_ext; split; intro.
split; apply Forall_sublist; auto.
 destruct H0.
 unfold sublist in *.
 rewrite Z.sub_0_r in H0.
 simpl in *.
 rewrite Z2Nat.inj_sub in H1 by omega.
 rewrite  Zlength_correct in *.
 rewrite Nat2Z.id in H1.
 assert (Z.to_nat n <= length data)%nat.
 apply Nat2Z.inj_le.
 rewrite Z2Nat.id by omega.
 apply H.
 clear H.
 pose proof (firstn_skipn (Z.to_nat n) data).
 rewrite <- H.
 apply Forall_app. split.
 auto.
 rewrite firstn_same in H1; auto.
 rewrite skipn_length.
 omega.
*
  unfold data_at at 1.
  erewrite field_at_Tarray; try reflexivity; try omega.
  rewrite (split2_array_at _ _ _ 0%Z n (Zlength data)) by omega.
  autorewrite with sublist. rewrite !sublist_map.
  forget (map Vint (map Int.repr (sublist 0 n data))) as L1.
  forget (map Vint (map Int.repr (sublist n (Zlength data) data))) as L2.
  unfold data_at.
(* need a more general version of field_at_Tarray *)
Admitted.

Lemma split3_data_block:
  forall lo hi sh data d,
  0 <= lo <= hi ->
  hi <= Zlength data ->
  field_compatible (tarray tuchar (Zlength data)) [] d ->
  data_block sh data d = 
  (data_block sh (sublist 0 lo data) d *
   data_block sh (sublist lo hi data) 
   (field_address0 (tarray tuchar (Zlength data)) [ArraySubsc lo] d) *
   data_block sh (sublist hi (Zlength data) data) 
   (field_address0 (tarray tuchar (Zlength data)) [ArraySubsc hi] d))%logic.
Proof.
  intros.
  rewrite (split2_data_block hi) by omega.
  rewrite (split2_data_block lo) by (autorewrite with sublist; omega).
  autorewrite with sublist.
  f_equal. f_equal.
  f_equal.
  unfold field_address0.
  rewrite !if_true; auto.
  eapply field_compatible0_cons_Tarray; try reflexivity; auto; try omega.
  eapply field_compatible0_cons_Tarray; try reflexivity; auto; try omega.
  hnf in H1|-*; intuition.
  clear- H2 H3 H1 H0.
  unfold legal_alignas_type in H1|-*; simpl in H1|-*.
  unfold tarray in *.
  rewrite nested_pred_ind in H1.
  rewrite nested_pred_ind.
  rewrite andb_true_iff in *. destruct H1; split; auto.
  clear - H2 H3 H H0.
  unfold local_legal_alignas_type in *. simpl in *.
  rewrite <- Zle_is_le_bool in H|-*. omega.
  clear - H6 H0 H2 H3.
  simpl sizeof in *. rewrite Z.max_r in * by omega. omega.
  destruct d; try contradiction; simpl in *.
  rewrite Z.max_r in * by omega. omega.
Qed.

Lemma offset_val_field_address0:
  forall {cs: compspecs} i n len t lo gfs t' p,
 nested_field_type2 t gfs = tarray t' len ->
 (n = sizeof cenv_cs t' * i)%Z ->
 0 <= lo <= len ->
 0 <= lo+i <= len ->
 offset_val (Int.repr n) (field_address0 t (ArraySubsc lo::gfs) p) =
  field_address0 t (ArraySubsc (lo+i) :: gfs) p.
Proof.
intros.
rename H2 into H1'.
unfold field_address0.
if_tac.
rewrite if_true.
normalize.
f_equal. f_equal.
hnf in H2.
decompose [and] H2; clear H2.
rewrite nested_field_offset2_ind; auto.
symmetry. 
rewrite nested_field_offset2_ind; auto.
rewrite <- Z.add_assoc.
f_equal.
rewrite H.
simpl. rewrite Z.mul_add_distr_l.
f_equal.  auto.
constructor; auto.
inv H11; auto.
rewrite H. constructor; auto; omega.
hnf in H2.
decompose [and] H2; clear H2.
inv H11.
hnf. repeat split; auto.
rewrite H in *.
inv H10; split; omega.
rewrite if_false; auto.
contradict H2.
hnf in H2.
decompose [and] H2; clear H2.
inv H11.
hnf. repeat split; auto.
rewrite H in *.
inv H10; split; auto; omega.
Qed.

Lemma update_loop_body_proof:
 forall (Espec : OracleKind) (sh: share) (hashed : list int) (frag data : list Z) (c d : val)
  (len : Z) kv (r_h : list int)
   (Delta : tycontext) (blocks bl : list int)
 (HDelta: Delta = initialized_list [_p; _n; _data]
                     (func_tycontext f_SHA256_Update Vprog Gtot))
 (Hsh: readable_share sh)
 (H: 0 <= len <= Zlength data)
 (Hdiv: (LBLOCKz | Zlength blocks))
 (H0: r_h = hash_blocks init_registers hashed)
 (H4: (LBLOCKz | Zlength hashed))
 (Hblocks: intlist_to_Zlist blocks =  frag ++ 
          sublist 0 (Zlength blocks * 4 - Zlength frag) data)
 (H3 : Zlength frag < CBLOCKz)
 (Hlen: len <= Int.max_unsigned)
 (Hlen_ge: len - (Zlength blocks * 4 - Zlength frag) >= 64)
 (H6: sublist (Zlength blocks * 4 - Zlength frag) 
                    (Zlength blocks * 4 - Zlength frag + CBLOCKz) data =
        intlist_to_Zlist bl)
 (H7: Zlength bl = LBLOCKz)
 (LEN64: bitlength hashed frag  + len * 8 < two_p 64),
 semax Delta
  (PROP  ()
   LOCAL 
   (temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
   temp _data (field_address0 (tarray tuchar (Zlength data)) [ArraySubsc (Zlength blocks * 4 - Zlength frag)] d);
   temp _c c;
   temp _len (Vint (Int.repr (len - (Zlength blocks * 4 - Zlength frag))));
   gvar _K256 kv)
   SEP  (`(K_vector kv);
   `(data_at Tsh t_struct_SHA256state_st
       (map Vint (hash_blocks init_registers (hashed ++ blocks)),
       (Vint (lo_part (bitlength hashed frag + len * 8)),
       (Vint (hi_part (bitlength hashed frag + len * 8)), 
        (list_repeat (Z.to_nat CBLOCKz) Vundef, Vundef)))) c);
   `(data_block sh data d))) 
  sha_update_loop_body
  (normal_ret_assert
   (@exp (environ->mpred) _ _  (fun a:list int => 
      PROP 
      (len >= Zlength a * 4 - Zlength frag;
       (LBLOCKz | Zlength a);
       intlist_to_Zlist a = frag ++ sublist 0 (Zlength a * 4 - Zlength frag) data;
       True)
      LOCAL 
      (temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
      temp _data (field_address0 (tarray tuchar (Zlength data)) [ArraySubsc (Zlength a * 4 - Zlength frag)] d);
      temp _c c;
      temp _len (Vint (Int.repr (len - (Zlength a * 4 - Zlength frag))));
      gvar _K256 kv)
      SEP  (`(K_vector kv);
      `(data_at Tsh t_struct_SHA256state_st
          (map Vint (hash_blocks init_registers (hashed ++ a)),
          (Vint (lo_part (bitlength hashed frag + len * 8)),
          (Vint (hi_part (bitlength hashed frag + len * 8)),
          (list_repeat (Z.to_nat CBLOCKz) Vundef, 
           Vundef)))) c);
      `(data_block sh data d))))).
Proof.
assert (H4:=true).
intros.
name c' _c.
name data_ _data_.
name len' _len.
name data' _data.
name p _p.
name n _n.
unfold sha_update_loop_body.
subst Delta; abbreviate_semax.
assert (Hblocks' := Hblocks_lem Hblocks).
assert_PROP (field_compatible (tarray tuchar (Zlength data)) [] d) as FC by entailer!.
set (lo := Zlength blocks * 4 - Zlength frag) in *.
 replace_SEP 2
  (`(data_block sh (sublist 0 lo data) d *
       data_block sh (sublist lo (lo+CBLOCKz) data)
         (field_address0 (tarray tuchar (Zlength data)) [ArraySubsc lo] d) *
       data_block sh (sublist (lo+CBLOCKz) (Zlength data) data)
         (field_address0 (tarray tuchar (Zlength data)) [ArraySubsc (lo+CBLOCKz)] d))).
  {entailer!.
   rewrite (split3_data_block lo (lo+CBLOCKz) sh data); auto;
     subst lo; Omega1.
  }
 rewrite H6.
 normalize.
forward_call (* sha256_block_data_order (c,data); *)
 (hashed++ blocks,  bl, c, 
  field_address0 (tarray tuchar (Zlength data))  [ArraySubsc lo] d,
  sh, kv).
 unfold data_at.
 unfold_field_at 1%nat.
 entailer!.
 split3; auto. apply divide_length_app; auto.
 simpl map. (* should not need this *)
 forward. (* data += SHA_CBLOCK; *)
 forward. (* len  -= SHA_CBLOCK; *)
 Exists (blocks++ bl).
 entailer!.
 subst lo. autorewrite with sublist.
 rewrite Z.mul_add_distr_r. 
 erewrite (offset_val_field_address0 CBLOCKz) by (try reflexivity; Omega1).
 repeat split; auto; try Omega1.
 apply Z.divide_add_r; auto. rewrite H7. apply Z.divide_refl.
 rewrite intlist_to_Zlist_app.
 rewrite Hblocks; rewrite <- H6.
 rewrite app_ass.
 f_equal. 
 rewrite <- sublist_split; try Omega1.
 f_equal. Omega1.
 f_equal. f_equal. f_equal. Omega1.
 f_equal. f_equal. 
 autorewrite with sublist. Omega1.
 unfold data_at. unfold_field_at 6%nat.
 rewrite (split3_data_block lo (lo+CBLOCKz) sh data d)
   by (auto; subst lo; Omega1).
 rewrite app_ass.
 rewrite H6.
 cancel.
Qed.

Definition update_outer_if :=
     Sifthenelse
        (Ebinop One (Etempvar _n tuint) (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
           (Sset _fragment
              (Ebinop Osub
                 (Ebinop Omul (Econst_int (Int.repr 16) tint)
                    (Econst_int (Int.repr 4) tint) tint) (Etempvar _n tuint)
                 tuint)) update_inner_if)
        Sskip.

Lemma update_outer_if_proof:
 forall  (Espec : OracleKind) (hashed : list int) 
           (dd data : list Z) (c d : val) (sh : share) (len : Z) kv
   (H : 0 <= len <= Zlength data)
   (Hsh: readable_share sh)
   (HBOUND : bitlength hashed dd + len * 8 < two_p 64)
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
   (Hlen : len <= Int.max_unsigned),
semax
  (initialized_list [_data; _p; _n]
     (func_tycontext f_SHA256_Update Vprog Gtot))
  (PROP  ()
   LOCAL 
   (temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
    temp _n (Vint (Int.repr (Zlength dd)));
    temp _data d; temp _c c;temp _data_ d;
    temp _len (Vint (Int.repr len));
    gvar _K256 kv)
   SEP  (`(data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + len*8)),
                   (Vint (hi_part (bitlength hashed dd + len*8)),
                    (map Vint (map Int.repr dd) ++ list_repeat (Z.to_nat (CBLOCKz-Zlength dd)) Vundef, 
                     Vint (Int.repr (Zlength dd))))))
               c);
   `(K_vector kv);
   `(data_block sh data d))) update_outer_if
  (overridePost (sha_update_inv sh hashed len c d dd data kv false)
     (function_body_ret_assert tvoid
        (EX  a' : s256abs,
         PROP  (update_abs (sublist 0 len data) (S256abs hashed dd) a')
         LOCAL ()
         SEP  (`(K_vector kv);
                `(sha256state_ a' c); `(data_block sh data d))))).
Proof.
intros.
unfold update_outer_if.
forward_if (sha_update_inv sh hashed len c d dd data kv false).
* (* then clause *)

forward.  (* fragment = SHA_CBLOCK-n; *)
drop_LOCAL 5%nat.
rewrite semax_seq_skip.
fold (inv_at_inner_if sh hashed len c d dd data kv).
apply semax_seq with (sha_update_inv sh hashed len c d dd data kv false).
change Delta with Delta_update_inner_if.
weak_normalize_postcondition.
pose (j := inv_at_inner_if sh hashed len c d dd data kv).
unfold inv_at_inner_if in j.
simple apply (update_inner_if_proof Espec hashed dd data c d sh len kv);
  try assumption.
forward. 
apply andp_left2; auto.
* (* else clause *)
forward.  (* skip; *)
apply exp_right with nil. rewrite <- app_nil_end.
assert (Int.unsigned (Int.repr (Zlength dd)) = Int.unsigned (Int.repr 0)) by (f_equal; auto).
repeat rewrite Int.unsigned_repr in H1 by Omega1.
rewrite H1 in *.
rewrite Zlength_correct in H1;  destruct dd; inv H1.
autorewrite with sublist.
simpl app; simpl intlist_to_Zlist.
clear H0.
Time entailer!.  (* 139 sec *)
split.
apply Z.divide_0_r.
unfold field_address0. rewrite if_true.
simpl. normalize.
eapply field_compatible0_cons_Tarray; try reflexivity; auto; try omega.
(* TODO:  see if a "stronger" proof system could work here
  rewrite data_at_field_at.
   apply field_at_stronger.
  ...
  with automatic cancel...
*)
 unfold data_at at 2; unfold_field_at 1%nat.
 unfold data_at at 1; unfold_field_at 1%nat.
 cancel.
Qed.

Lemma update_while_proof:
 forall (Espec : OracleKind) (hashed : list int) (dd data: list Z) kv
    (c d : val) (sh : share) (len : Z) 
  (H : 0 <= len <= Zlength data)
   (Hsh: readable_share sh)
  (HBOUND : bitlength hashed dd + len * 8 < two_p 64)
  (c' : name _c) (data_ : name _data_) (len' : name _len)  
  (data' : name _data) (p : name _p) (n : name _n)  (fragment : name _fragment)
  (H3 : Zlength dd < CBLOCKz)
  (H3' : Forall isbyteZ dd) 
  (H4 : (LBLOCKz | Zlength hashed)) 
  (Hlen : len <= Int.max_unsigned),
 semax
     (initialized_list [_p; _n; _data]
       (func_tycontext f_SHA256_Update Vprog Gtot))
  (sha_update_inv sh hashed len c d dd data kv false)
  (Swhile
     (Ebinop Oge (Etempvar _len tuint)
        (Ebinop Omul (Econst_int (Int.repr 16) tint)
           (Econst_int (Int.repr 4) tint) tint) tint) sha_update_loop_body)
  (normal_ret_assert (sha_update_inv sh hashed len c d dd data kv true)).
Proof.
intros.
abbreviate_semax.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
unfold sha_update_inv.
Intro blocks.
repeat (apply semax_extract_PROP; intro).
rewrite semax_seq_skip. (* should be part of forward_while *)
forward_while
    (sha_update_inv sh hashed len c d dd data kv false)
   blocks'.
*
 Exists blocks. entailer!.
*
  entailer!.
*
 normalize_postcondition.
 clear dependent blocks.
 rename blocks' into blocks.
  pose proof (Hblocks_lem H8).
 assert (H0': (Zlength dd <= Zlength blocks * 4)%Z) by Omega1.
 clear H0; rename H0' into H0.
 rewrite Int.unsigned_repr in HRE by omega.
 assert_PROP (Forall isbyteZ data).
  rewrite (data_block_isbyteZ sh data d).
  entailer!.
 rename H1 into BYTESdata.
 pose (bl := Zlist_to_intlist (sublist (Zlength blocks * 4 - Zlength dd) 
                                                   (Zlength blocks * 4 - Zlength dd + CBLOCKz) data)).
assert (Zlength bl = LBLOCKz). {
 apply Zlength_Zlist_to_intlist.
 pose proof CBLOCKz_eq; pose proof LBLOCKz_eq;
  autorewrite with sublist. reflexivity.
}
simple apply (update_loop_body_proof Espec sh hashed dd data c d len kv (hash_blocks init_registers hashed) Delta blocks bl); 
   try assumption; auto.
+
 unfold bl; rewrite Zlist_to_intlist_to_Zlist; auto.
 pose proof CBLOCKz_eq;  autorewrite with sublist.
 exists LBLOCKz; reflexivity.
 apply Forall_sublist; auto.
*
 assert  (Zlength blocks' * 4 >= Zlength dd).
   rewrite <- (Zlength_intlist_to_Zlist blocks').
   rewrite H8. autorewrite with sublist. Omega1.
 unfold sha_update_inv.
 clear dependent blocks.
 forward.
 Exists blocks'.
 entailer!.
 apply negb_false_iff in HRE. (* should not be necessary *)
 apply ltu_repr in HRE; Omega1.
Qed.
