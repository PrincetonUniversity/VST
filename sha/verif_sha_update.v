Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.verif_sha_update2.
Require Import sha.verif_sha_update3.
Require Import sha.verif_sha_update4.
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

Lemma offset_val_array_at_tuchar:
  forall (ofs : Z) (sh : Share.t) (f : Z -> val) (lo hi : Z) (v : val),
  array_at tuchar sh (fun i : Z => f (i - ofs)%Z) (ofs + lo) (ofs + hi) v =
  array_at tuchar sh f lo hi (offset_val (Int.repr ofs) v).
Proof.
intros.
rewrite offset_val_array_at.
f_equal. f_equal. f_equal. apply Z.mul_1_l.
Qed.

Lemma update_last_if_proof:
 forall  (Espec : OracleKind) (hashed : list int) 
           (dd data : list Z) (c d : val) (sh : share) (len : nat)
   (H : len <= length data)
   (HBOUND : (s256a_len (S256abs hashed dd) + Z.of_nat len * 8 < two_p 64)%Z)
   (c' : name _c)
   (data_ : name _data_)
   (len' : name _len)
   (data' : name _data)
   (p : name _p)
   (n : name _n)
   (fragment : name _fragment)
   (hi : int)
   (lo : int)
   (H7 : ((Zlength hashed * 4 + Zlength dd) * 8)%Z = hilo hi lo)
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
   LOCAL  (`(eq (offset_val (Int.repr 40) c)) (eval_id _p);
   `(eq c) (eval_id _c);
   `(eq (offset_val (Int.repr (Z.of_nat (length blocks * 4 - length dd))) d))
     (eval_id _data);
   `(eq (Vint (Int.repr (Z.of_nat (len - (length blocks * 4 - length dd))))))
     (eval_id _len))
   SEP  (`K_vector (eval_var _K256 (tarray tuint 64));
   `(array_at tuint Tsh
       (tuints (hash_blocks init_registers (hashed ++ blocks))) 0 8 c);
   `(sha256_length (hilo hi lo + Z.of_nat len * 8) c);
   `(array_at_ tuchar Tsh 0 64 (offset_val (Int.repr 40) c));
   `(field_at Tsh t_struct_SHA256state_st _num)
     (`force_val
        (`(sem_cast (typeof (Etempvar _len tuint)) tuint)
           (eval_expr (Etempvar _len tuint))))
     (eval_lvalue
        (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
           t_struct_SHA256state_st)); `(data_block sh data d)))
  update_last_if
  (normal_ret_assert
     (EX  a' : s256abs,
      PROP  (update_abs (firstn len data) (S256abs hashed dd) a')
      LOCAL ()
      SEP  (`K_vector (eval_var _K256 (tarray tuint 64));
             `(sha256state_ a' c); `(data_block sh data d)))).
Proof.
intros.
unfold update_last_if; simplify_Delta; abbreviate_semax.
forward_if'.
(*  - quick_typecheck.

 entailer. (* if-condition evaluates *)
*)
 - (* then-clause *)
   unfold data_block; simpl; normalize.
  rename H0 into Dbytes.
 set (b4d := length blocks * 4 - length dd) in *.
   forward_call (* memcpy (p,data,len); *)
(*   WITH sh : share*share, p: val, q: val, n: Z, contents: Z -> int  *)
  ((sh,Tsh), offset_val (Int.repr 40) c, 
                          offset_val (Int.repr (Z.of_nat b4d)) d,
                          Z.of_nat (len - b4d), 
                          force_int oo (fun i => ZnthV tuchar (map Vint (map Int.repr data))
                                 (i + Z.of_nat b4d))). {
 simpl @snd.
 autorewrite with norm subst.
 unfold app at 2 3 4.
 entailer.
(* rewrite H1. *)
 clear H1; pose (H5:=True).
assert (H1: (Z.of_nat len >= Z.of_nat b4d)%Z) by
 (rewrite <- Nat2Z.inj_ge; auto).
 unfold tuchars.
 assert (H99: (Z.of_nat CBLOCK < Int.max_unsigned)%Z )
   by (change (Z.of_nat CBLOCK) with 64%Z; compute; congruence).
assert (H12: 0 <= len - b4d < 64)
  by (change 64 with CBLOCK; omega).
 rewrite prop_true_andp.
Focus 2. {
 rewrite Int.unsigned_repr; [auto | split; [clear; omega | ]].
 apply Z.le_trans with (Z.of_nat 64). 
 apply -> Nat2Z.inj_le; clear - H12; omega.
 change CBLOCK with 64 in H99; clear - H99; omega.
} Unfocus.
 rewrite memory_block_array_tuchar';
  [ | destruct c; try contradiction Pc; apply I 
  | change 0%Z with (Z.of_nat 0); apply -> Nat2Z.inj_ge; clear - H12; omega].
 rewrite <- offset_val_array_at_tuchar.
 rewrite Z.add_0_r.
 rewrite Nat2Z.inj_sub by omega.
 rewrite (split_array_at_ (Z.of_nat len - Z.of_nat b4d)  _ _ 0 64)%Z.
 rewrite (split_array_at (Z.of_nat b4d) _ sh).
 rewrite (split_array_at (Z.of_nat len) _ sh _ _ (Zlength data)).
 repeat rewrite <- sepcon_assoc.
 fold b4d.
 replace (Z.of_nat b4d + (Z.of_nat len - Z.of_nat b4d))%Z with (Z.of_nat len) by (clear; omega).
match goal with |- _ |-- ?A d * _ * _ =>
  replace A with (array_at tuchar sh (ZnthV tuchar (map Vint (map Int.repr data))) (Z.of_nat b4d)
  (Z.of_nat len))
end.
 cancel.
 apply array_at_ext; intros.
 unfold ZnthV, Basics.compose, cVint, force_int.
  rewrite Z.sub_add.
 if_tac; try reflexivity.
 unfold b4d in *; clear b4d.
 elimtype False; clear - H6 H2 H1; omega.
 rewrite map_map.
 rewrite (nth_map' (fun x => Vint (Int.repr x)) _ 0%Z); auto.
 apply Nat2Z.inj_lt.  rewrite Z2Nat.id by (clear - H6; omega).
 apply Z.lt_le_trans with (Z.of_nat len); [ destruct H2; auto | ].
 apply Nat2Z.inj_le. auto.
 split; auto.  apply Nat2Z.inj_le; auto.
 rewrite Zlength_correct; apply Nat2Z.inj_le; auto.
 split; [clear; omega | ].
 apply Z.le_trans with (Z.of_nat len); [clear - H1; omega | ].
 rewrite Zlength_correct; apply Nat2Z.inj_le; auto.
 split; [clear - H1; omega | ] .
 rewrite <- Nat2Z.inj_sub.
 change 64%Z with (Z.of_nat 64). apply Nat2Z.inj_le; clear - H12; omega.
 apply Nat2Z.inj_le; clear - H1; omega.
} 
after_call.
apply exp_right 
  with (S256abs (hashed++blocks)
              (firstn (len - (length blocks * 4 - length dd))
                (skipn (length blocks * 4 - length dd) data))).
entailer.
clear TC1 TC0.
 rewrite prop_true_andp. 
Focus 2. {
 apply Update_abs; auto.
 rewrite Zlength_correct; change CBLOCKz with (Z.of_nat CBLOCK);
  apply Nat2Z.inj_lt;
 rewrite firstn_length. rewrite min_l.
 auto.
 rewrite skipn_length.
 clear - H; omega.
 unfold b4d in *;  omega.
 rewrite Hblocks.
 repeat rewrite app_ass.
 f_equal.
 rewrite firstn_app.
 f_equal.
 clear - Hblocks_len.
 fold b4d; omega.
} Unfocus.
rewrite <- offset_val_array_at_tuchar.
pull_right (K_vector (eval_var _K256 (tarray tuint 64) rho)).
apply sepcon_derives; auto.
clear H0 rho. pose (H0:=True).
unfold data_block, tuchars.
rewrite prop_true_andp by auto.
replace (array_at tuchar sh
  (fun i : Z =>
   cVint
     (force_int
      oo (fun i0 : Z =>
          ZnthV tuchar (map Vint (map Int.repr data)) (i0 + Z.of_nat b4d)))
     (i - Z.of_nat b4d)) (Z.of_nat b4d + 0)
  (Z.of_nat b4d + Z.of_nat (len - b4d)))
  with (array_at tuchar sh (ZnthV tuchar (map Vint (map Int.repr data))) (Z.of_nat b4d) (Z.of_nat len)).
Focus 2. {
rewrite Nat2Z.inj_sub by omega.
replace (Z.of_nat b4d + (Z.of_nat len - Z.of_nat b4d))%Z with (Z.of_nat len) by (clear; omega).
rewrite Z.add_0_r.
apply array_at_ext; intros.
unfold cVint, force_int, Basics.compose, ZnthV.
rewrite Z.sub_add.
rewrite if_false by omega.
rewrite map_map.
rewrite (nth_map' _ _ 0%Z); auto.
destruct H2. apply Z2Nat.inj_lt in H5; try omega.
rewrite Nat2Z.id in H5; omega.
} Unfocus.
pull_left (array_at tuchar sh (ZnthV tuchar (map Vint (map Int.repr data))) 0
  (Z.of_nat b4d) d).
rewrite <- split_array_at by omega.
pull_left (array_at tuchar sh (ZnthV tuchar (map Vint (map Int.repr data)))
  (Z.of_nat len) (Zlength data) d).
pull_left (array_at tuchar sh (ZnthV tuchar (map Vint (map Int.repr data)))
  0 (Z.of_nat len) d).
rewrite <- split_array_at
 by (split; [omega | rewrite Zlength_correct; apply Nat2Z.inj_le; auto]).
pull_right (array_at tuchar sh (ZnthV tuchar (map Vint (map Int.repr data))) 0
  (Zlength data) d); apply sepcon_derives; auto.
unfold sha256_length.
normalize. rename x0 into hi'; rename x into lo'.
unfold sha256state_.
set (dd' := firstn (len - (length blocks * 4 - length dd))
              (skipn (length blocks * 4 - length dd) data)).
 apply exp_right with 
              (map Vint (hash_blocks init_registers (hashed ++ blocks)),
                (Vint lo', (Vint hi', (map Vint (map Int.repr dd'), 
                 Vint (Int.repr (Zlength dd')))))).
assert (Z.of_nat (len-b4d) = Zlength dd'). {
unfold dd'.
rewrite Zlength_correct.
rewrite firstn_length. rewrite min_l.
reflexivity.
rewrite skipn_length. 
apply minus_le_compat_r.
omega.
fold b4d. omega.
}
rewrite prop_true_andp.
simpl_data_at.
unfold at_offset.
rewrite (split_array_at (Z.of_nat (len-b4d)) _ _ _ 0 64)%Z.
replace (array_at tuchar Tsh
  (cVint
     (force_int
      oo (fun i : Z =>
          ZnthV tuchar (map Vint (map Int.repr data)) (i + Z.of_nat b4d)))) 0
  (Z.of_nat (len - b4d)))
 with (array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd'))) 0
         (Z.of_nat (len - b4d))).
Focus 2. {
apply array_at_ext; intros.
unfold cVint, force_int, Basics.compose, ZnthV.
rewrite if_false by omega.
rewrite if_false by omega.
rewrite map_map. rewrite map_map.
rewrite (nth_map' _ _ 0%Z).
rewrite (nth_map' _ _ 0%Z).
f_equal; f_equal.
unfold dd'.
rewrite nth_firstn_low.
rewrite nth_skipn.
f_equal.
fold b4d.
rewrite Z2Nat.inj_add.
rewrite Nat2Z.id. auto.
apply H6.
omega.
fold b4d.
rewrite skipn_length. 
split; try omega.
destruct H6.
apply Z2Nat.inj_lt in H8; try omega.
rewrite Nat2Z.id in H8; auto.
omega.
rewrite <- (Nat2Z.id (length data)).
rewrite <- Zlength_correct.
apply Z2Nat.inj_lt.
omega.
clear; rewrite Zlength_correct; omega.
destruct H6 as [_ H8].
rewrite Nat2Z.inj_sub in H8 by omega.
apply Nat2Z.inj_ge in Hblocks_len.
clear - Hblocks_len H8 H.
apply Nat2Z.inj_le in H.
rewrite <- Zlength_correct in H.
omega. 
rewrite <- (Nat2Z.id (length dd')).
rewrite <- Zlength_correct.
apply Z2Nat.inj_lt; try omega.
} Unfocus.
rewrite <- Nat2Z.inj_sub by omega.
rewrite H5.
cancel.
apply derives_refl'; apply equal_f; apply array_at_ext; intros.
unfold ZnthV. rewrite if_false by omega.
rewrite nth_overflow; auto.
repeat rewrite map_length.
rewrite <- (Nat2Z.id (length dd')).
apply Z2Nat.inj_le; try  omega.
rewrite <- Zlength_correct; destruct H6; auto.
split; [clear; omega|].
change 64%Z with (Z.of_nat CBLOCK).
apply Nat2Z.inj_le; auto.
clear - DONE; omega.
unfold s256_relate; repeat split; auto.
exists hi',lo'; repeat split; auto.
rewrite H2.  rewrite <- H7.
rewrite <- Z.mul_add_distr_r.
f_equal.
rewrite initial_world.Zlength_app.
rewrite Z.mul_add_distr_r.
repeat rewrite <- Z.add_assoc.
f_equal.
rewrite <- H5.
rewrite Nat2Z.inj_sub by omega.
unfold b4d.
rewrite Nat2Z.inj_sub by omega.
rewrite Nat2Z.inj_mul.
repeat rewrite <- Zlength_correct.
change (Z.of_nat 4) with 4%Z;
omega.
rewrite Zlength_correct in H5.
apply Nat2Z.inj in H5.
rewrite Zlength_correct; change CBLOCKz with (Z.of_nat CBLOCK);
 apply Nat2Z.inj_lt.
omega.
unfold dd'.
apply Forall_firstn.
apply Forall_skipn.
auto.
apply divide_length_app; auto.

 - (* else-clause *)
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
 assert (H7': len = length blocks * 4 - length dd).
   rewrite Nat2Z.inj_sub in H2' by auto.
    apply Nat2Z.inj. clear - H2'; omega.
 apply andp_right.
 apply prop_right.
 constructor; auto.
 rewrite Zlength_nil; change CBLOCKz with 64%Z; clear; omega.
 rewrite <- app_nil_end.
 rewrite Hblocks.
 rewrite <- H7'.
 reflexivity.
 unfold sha256state_.
 cancel.
 unfold sha256_length.
 normalize.
 apply exp_right with 
              (map Vint (hash_blocks init_registers (hashed ++ blocks)),
                (Vint x, (Vint x0, (nil, 
                 Vint Int.zero)))).
 simpl_data_at; unfold s256_relate.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd.
 apply andp_right; [apply prop_right | cancel].
 repeat split; simpl; auto.
 exists x0,x. split3; auto.
 rewrite Zlength_nil. rewrite H5. 
 rewrite <- H7.
 rewrite H7'.
 rewrite initial_world.Zlength_app.
 rewrite Z.mul_add_distr_r.
 rewrite Nat2Z.inj_sub by omega.
 rewrite Nat2Z.inj_mul. change (Z.of_nat 4) with 4%Z.
 rewrite (Zlength_correct blocks), (Zlength_correct dd).
 clear; omega.
 apply divide_length_app; auto.
 rewrite H2'.
 cancel.
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
rename H0 into HBOUND.

fold update_inner_if_then in *.
fold update_inner_if_else in *.
fold update_inner_if in *.
fold sha_update_loop_body in *.
forward.  (* data=data_; *)

unfold sha256_length, sha256state_.
normalize.
intros [r_h [r_Nl [r_Nh [r_data r_num]]]].
normalize.
unfold s256a_len.
unfold s256_relate in H0.
destruct a as [hashed dd].
simpl_data_at.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd in H0|-*.
destruct H0 as [H0 [H1 [H8 [[H3 H3'] [H4 H5]]]]].
destruct H1 as [hi [lo [H1 [H6 H7]]]].
subst r_Nh r_Nl.
rename H8 into H1.
subst r_data.
subst r_h r_num.
apply (assert_PROP (Z.of_nat len <= Int.max_unsigned)%Z); 
   [ | intro Hlen]. {
entailer!.
rewrite H1. apply Int.unsigned_range_2.
}

forward_call  (* SHA256_addlength(c, len); *)
  (Z.of_nat len, c, hilo hi lo). {
entailer!.
* rewrite <- H7. repeat rewrite <- (Z.mul_comm 8). rewrite <- (Z.mul_comm 4).
 rewrite Z.mul_add_distr_l. rewrite Z.mul_assoc.  change (8*4)%Z with 32%Z.
 repeat rewrite Zlength_correct;  omega.
* simpl in HBOUND. rewrite <- H7. apply HBOUND.
* unfold sha256_length.
 normalize; apply exp_right with lo. 
 normalize; apply exp_right with hi.
 entailer!.
}
after_call.
cbv beta iota. normalize.
forward. (* n = c->num; *)
forward. (* p=c->data; *)
entailer. 
simpl.
replace Delta with (initialized _p (initialized _n (initialized _data
                     (func_tycontext f_SHA256_Update Vprog Gtot))))
 by (simplify_Delta; reflexivity).
fold update_outer_if.
apply semax_seq with (sha_update_inv sh hashed len c d dd data hi lo false).
unfold POSTCONDITION, abbreviate.
eapply semax_pre; [ | simple apply update_outer_if_proof; assumption].
entailer!.
(* after if (n!=0) *)
eapply semax_seq' with
     (sha_update_inv sh hashed len c d dd data hi lo true).
clear POSTCONDITION MORE_COMMANDS Delta.
simple apply update_while_proof; assumption.
simplify_Delta; abbreviate_semax.
unfold sha_update_inv.   apply extract_exists_pre; intro blocks.
apply semax_extract_PROP; apply intro_update_inv; intros.
forward.    (* c->num=len; *)

apply semax_seq with (EX  a' : s256abs,
                    PROP  (update_abs (firstn len data) (S256abs hashed dd) a')
                    LOCAL ()
                    SEP 
                    (`K_vector (eval_var _K256 (tarray tuint 64));
                     `(sha256state_ a' c); `(data_block sh data d))).

replace Delta with (initialized _p (initialized _n (initialized _data
                     (func_tycontext f_SHA256_Update Vprog Gtot))))
 by (simplify_Delta; reflexivity).
 unfold POSTCONDITION, abbreviate; clear POSTCONDITION Delta MORE_COMMANDS.

make_sequential.
rewrite overridePost_normal'.
fold update_last_if.

simple apply update_last_if_proof; assumption.
abbreviate_semax.
(* after the last if *)
 apply extract_exists_pre; intro a'.
 forward.  (* return; *)
 apply exp_right with a'.
 entailer!.
Qed.
