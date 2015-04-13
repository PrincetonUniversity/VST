Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.verif_sha_update2.
Require Import sha.verif_sha_update3.
Local Open Scope nat.
Local Open Scope logic.


Lemma Hblocks_lem:
 forall {blocks: list int} {frag: list Z} {data},
 intlist_to_Zlist blocks = frag ++ firstn (length blocks * 4 - length frag) data ->
 length frag <= length blocks * 4.
Proof.
intros.
assert (length (intlist_to_Zlist blocks) = 
               length ( frag ++
     firstn (length blocks * 4 - length frag) data)) by congruence.
 rewrite length_intlist_to_Zlist, app_length in H0.
 rewrite mult_comm; omega.
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

Lemma update_loop_body_proof:
 forall (Espec : OracleKind) (sh: share) (hashed : list int) (frag data : list Z) (c d : val)
  (len : Z) kv (r_h : list int)
   (Delta : tycontext) (blocks bl : list int)
 (HDelta: Delta = initialized_list [_p; _n; _data]
                     (func_tycontext f_SHA256_Update Vprog Gtot))
 (H: (0 <= len <= Zlength data)%Z)
 (Hdiv: (LBLOCKz | Zlength blocks))
 (H0: r_h = hash_blocks init_registers hashed)
 (H4: (LBLOCKz | Zlength hashed))
 (Hblocks: intlist_to_Zlist blocks =  frag ++ firstn (length blocks * 4 - length frag) data)
 (H3 : (Zlength frag < CBLOCKz)%Z)
 (Hlen: (len <= Int.max_unsigned)%Z)
 (Hlen_ge: (len - Z.of_nat (length blocks * 4 - length frag) >= 64)%Z)
 (H6: firstn CBLOCK (skipn (length blocks * 4 - length frag) data) =
     intlist_to_Zlist bl)
 (H7: Zlength bl = LBLOCKz)
 (LEN64: (bitlength hashed frag  + len * 8 < two_p 64)%Z),
 semax Delta
  (PROP  ()
   LOCAL 
   (temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
   temp _data
     (offset_val (Int.repr (Z.of_nat (length blocks * 4 - length frag))) d);
   temp _c c;
   temp _len (Vint (Int.repr (len - (Zlength blocks * 4 - Zlength frag))));
   gvar _K256 kv)
   SEP  (`(K_vector kv);
   `(data_at Tsh t_struct_SHA256state_st
       (map Vint (hash_blocks init_registers (hashed ++ blocks)),
       (Vint (lo_part (bitlength hashed frag + len * 8)),
       (Vint (hi_part (bitlength hashed frag + len * 8)), ([], Vundef)))) c);
   `(data_block sh data d))) sha_update_loop_body
  (normal_ret_assert
     (EX  a : list int,
      PROP 
      ((len >= Zlength a * 4 - Zlength frag)%Z;
       (LBLOCKz | Zlength a);
       intlist_to_Zlist a = frag ++ firstn (length a * 4 - length frag) data;
       True)
      LOCAL 
      (temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
      temp _data
        (offset_val (Int.repr (Z.of_nat (length a * 4 - length frag))) d);
      temp _c c;
      temp _len (Vint (Int.repr (len - (Zlength a * 4 - Zlength frag))));
      gvar _K256 kv)
      SEP  (`(K_vector kv);
      `(data_at Tsh t_struct_SHA256state_st
          (map Vint (hash_blocks init_registers (hashed ++ a)),
          (Vint (lo_part (bitlength hashed frag + len * 8)),
          (Vint (hi_part (bitlength hashed frag + len * 8)), ([], Vundef)))) c);
      `(data_block sh data d)))).
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
 rewrite (split3_data_block (length blocks * 4 - length frag) CBLOCK sh data) by MyOmega.
normalize.
 rewrite Zlength_correct in H3; change CBLOCKz with (Z.of_nat CBLOCK) in H3;
  apply Nat2Z.inj_lt in H3.
 rewrite H6.
rename H2 into H98; rename H4 into H99.

forward_call' (* sha256_block_data_order (c,data); *)
 (hashed++ blocks,  bl, c, 
  offset_val (Int.repr (Z.of_nat (length blocks * 4 - length frag))) d,
  sh, kv).
 unfold_data_at 1.
entailer!.
split; auto.
apply divide_length_app; auto.
 simpl map.

 forward data_old. (* data += SHA_CBLOCK; *)
 forward len_old. (* len  -= SHA_CBLOCK; *)
 unfold loop1_ret_assert.
 unfold sha_update_inv.
 apply exp_right with (blocks++ bl).
 entailer.
 clear TC1 TC.
 assert (Hblocks' := Hblocks_lem Hblocks).
 unfold_data_at 1.
 rewrite Nat2Z.inj_sub in Hlen_ge by Omega1.
 rewrite Nat2Z.inj_mul in Hlen_ge.
 change (Z.of_nat 4) with 4%Z in Hlen_ge.
 apply andp_right; [ apply prop_right; repeat split | cancel].
*
 rewrite Zlength_app. rewrite Z.mul_add_distr_r.
 Omega1. 
* apply divide_length_app; auto. rewrite H7. exists 1%Z; reflexivity.
*
 rewrite intlist_to_Zlist_app.
 rewrite Hblocks; rewrite <- H6.
 rewrite app_ass.
 f_equal. rewrite app_length. apply Zlength_length in H7; auto.
  rewrite H7.
  rewrite  mult_plus_distr_r. change (LBLOCK*4)%nat with CBLOCK.
 rewrite NPeano.Nat.add_sub_swap by auto.
 apply firstn_app.
*
 destruct d; inv Pd; simpl. f_equal.
  f_equal.
 rewrite app_length.
 apply Zlength_length in H7; auto.
 rewrite H7.
 f_equal.
 rewrite  mult_plus_distr_r. Omega1.
*
 f_equal.
 rewrite Zlength_app. rewrite Z.mul_add_distr_r. Omega1.
*
 rewrite app_ass.
 rewrite (split3_data_block (length blocks * 4 - length frag) CBLOCK sh data)
    by Omega1.
 rewrite H6.
 normalize.
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
   (H4 : (LBLOCKz | Zlength hashed))
   (Hlen : (len <= Int.max_unsigned)%Z),
semax
  (initialized_list [_p; _n; _data]
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
                    (map Vint (map Int.repr dd), 
                     Vint (Int.repr (Zlength dd))))))
               c);
   `(K_vector kv);
   `(data_block sh data d))) update_outer_if
  (overridePost (sha_update_inv sh hashed len c d dd data kv false)
     (function_body_ret_assert tvoid
        (EX  a' : s256abs,
         PROP  (update_abs (firstn (Z.to_nat len) data) (S256abs hashed dd) a')
         LOCAL ()
         SEP  (`(K_vector kv);
                `(sha256state_ a' c); `(data_block sh data d))))).
Proof.
intros.
unfold update_outer_if.
forward_if (sha_update_inv sh hashed len c d dd data kv false).
* (* then clause *)

forward.  (* fragment = SHA_CBLOCK-n; *)
match goal with |- context [temp _fragment (Vint (Int.repr ?A))] =>
   change A with (64-(Zlength dd))%Z
end.
drop_LOCAL 5%nat.
rewrite semax_seq_skip.
fold (inv_at_inner_if sh hashed len c d dd data kv).
apply semax_seq with (sha_update_inv sh hashed len c d dd data kv false).
change Delta with Delta_update_inner_if.
weak_normalize_postcondition.
simple apply (update_inner_if_proof Espec hashed dd data c d sh len kv);
  try assumption.
forward. 
apply andp_left2; auto.
* (* else clause *)
forward.  (* skip; *)
apply exp_right with nil. rewrite <- app_nil_end.
entailer.
assert (Int.unsigned (Int.repr (Zlength dd)) = Int.unsigned (Int.repr 0)) by (f_equal; auto).
repeat rewrite Int.unsigned_repr in H7 by Omega1.
rewrite Zlength_correct in H7;  destruct dd; inv H7.
rewrite Zlength_nil.
 entailer!.
 apply Z.divide_0_r.
 f_equal; omega.
 rewrite <- app_nil_end.
(* TODO:  see if a "stronger" proof system could work here
  rewrite data_at_field_at.
   apply field_at_stronger.
  ...
  with automatic cancel...
*)
 unfold_data_at 1.
 unfold_data_at 1.
 cancel.
Qed.

Lemma update_while_proof:
 forall (Espec : OracleKind) (hashed : list int) (dd data: list Z) kv
    (c d : val) (sh : share) (len : Z) 
  (H : (0 <= len <= Zlength data)%Z)
  (HBOUND : (bitlength hashed dd + len * 8 < two_p 64)%Z)
  (c' : name _c) (data_ : name _data_) (len' : name _len)  
  (data' : name _data) (p : name _p) (n : name _n)  (fragment : name _fragment)
  (H3 : (Zlength dd < CBLOCKz)%Z)
  (H3' : Forall isbyteZ dd) 
  (H4 : (LBLOCKz | Zlength hashed)) 
  (Hlen : (len <= Int.max_unsigned)%Z),
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
apply extract_exists_pre; intro blocks.
repeat (apply semax_extract_PROP; intro).
rewrite semax_seq_skip. (* should be part of forward_while *)
forward_while
    (sha_update_inv sh hashed len c d dd data kv false)
   (sha_update_inv sh hashed len c d dd data kv true)
   blocks'.
*
 apply exp_right with blocks.
 entailer!.
*
  entailer!.
*
 clear dependent blocks.
 apply exp_right with blocks'.
 entailer!.
 rewrite Int.unsigned_repr in HRE.
 apply HRE.
 split; try omega.
 assert (Hblocks' := Hblocks_lem H8).
 Omega1.
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
 pose (bl := Zlist_to_intlist (firstn CBLOCK (skipn (length blocks * 4 - length dd) data) )).

assert (CBLOCK <= length (skipn (length blocks * 4 - length dd) data)).
 {
  pose proof (Hblocks_lem H8). 
  rewrite skipn_length.
  Omega1. 
}
assert (Zlength bl = LBLOCKz). {
 apply Zlength_length; auto.
 unfold bl.
 apply length_Zlist_to_intlist. 
 rewrite firstn_length.
 rewrite min_l by auto. reflexivity.
}
simple apply (update_loop_body_proof Espec sh hashed dd data c d len kv (hash_blocks init_registers hashed) Delta blocks bl); 
   try assumption; auto.
+
 rewrite Nat2Z.inj_sub by MyOmega. MyOmega.
+
 unfold bl; rewrite Zlist_to_intlist_to_Zlist; auto.
 rewrite firstn_length.
 rewrite min_l by auto.
 exists LBLOCK; reflexivity.
 apply Forall_firstn.
 apply Forall_skipn; auto.
*
 unfold sha_update_inv.
 clear dependent blocks.
 apply extract_exists_pre; intro blocks.
 forward.
 apply exp_right with blocks.
 entailer!.
Qed.
