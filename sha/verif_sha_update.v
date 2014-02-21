Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.sha_lemmas.
Require Import sha.spec_sha.
Local Open Scope nat.
Local Open Scope logic.

Definition sha_update_inv sh hashed len c d (frag: list Z) (data: list Z) r_Nh r_Nl (done: bool) :=
   (EX blocks:list int,
   PROP  (len >= length blocks*4 - length frag /\
              NPeano.divide LBLOCK (length blocks) /\ 
              intlist_to_Zlist blocks = frag ++ firstn (length blocks * 4 - length frag) data /\
             if done then len-(length blocks*4 - length frag) < CBLOCK else True)
   LOCAL  (`(eq (offset_val (Int.repr 40) c)) (eval_id _p);
   `(eq c) (eval_id _c); `(eq (offset_val (Int.repr (Z.of_nat (length blocks*4-length frag))) d)) (eval_id _data);
   `(eq (Vint (Int.repr (Z.of_nat (len- (length blocks*4 - length frag)))))) (eval_id _len))
   SEP  (K_vector;
    `(array_at tuint Tsh (tuints (process_msg init_registers (hashed ++ blocks))) 0 8 c);
    `(sha256_length (hilo r_Nh r_Nl + (Z.of_nat len)*8) c);
   `(array_at_ tuchar Tsh 0 64 (offset_val (Int.repr 40) c));
   `(field_at_ Tsh t_struct_SHA256state_st _num c);
   `(data_block sh data d))).

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

(*
Lemma Hblocks'lem:
 forall {blocks frag: list int} {data},
 intlist_to_Zlist blocks = map Int.unsigned frag ++ firstn (length blocks * 4 - length frag) data ->
 length frag <= length blocks * 4.
Proof.
intros.
assert (length (intlist_to_Zlist blocks) = 
               length (   map Int.unsigned frag ++
     firstn (length blocks * 4 - length frag) data)) by congruence.
 rewrite length_intlist_to_Zlist, app_length in H0.
 rewrite map_length in H0.
 rewrite mult_comm; omega.
Qed.
*)

Lemma intro_update_inv:
 forall (len: nat) (blocks : list int) (frag data: list Z) (P' Q: Prop),
  (forall (Hblocks_len: len >= length blocks * 4 - length frag)
            (Hdiv: NPeano.divide LBLOCK (length blocks))
            (Hblocks: intlist_to_Zlist blocks = frag ++ firstn (length blocks * 4 - length frag) data)
            (DONE: P')
            (Hblocks': length blocks * 4 >= length frag),
            Q) ->
    (len >= length blocks*4 - length frag /\
    NPeano.divide LBLOCK (length blocks) /\ 
    intlist_to_Zlist blocks = frag ++ firstn (length blocks * 4 - length frag) data /\
              P' -> Q). 
Proof.
intros.
 destruct H0 as  [Hblocks_len [Hdiv [Hblocks DONE]]].
 apply H; clear H; auto.
 apply Hblocks_lem in Hblocks; auto.
Qed.

Lemma SHA256_Update_aux:
 forall (Espec : OracleKind) (sh: share) (hashed : list int) (r_data data : list Z) (c d : val)
  (len : nat) (r_h : list int) (r_Nl r_Nh : int)
   (Delta : tycontext) (blocks bl : list int)
 (HDelta: Delta = initialized _p (initialized _n (initialized _data
                     (func_tycontext f_SHA256_Update Vprog Gtot))))
 (H: len <= length data)
 (Hdiv: NPeano.divide LBLOCK (length blocks))
 (HBOUND: (s256a_len (S256abs hashed r_data) < BOUND)%Z)
 (H0: r_h = process_msg init_registers hashed)
 (H1: (Zlength (intlist_to_Zlist hashed ++ r_data)*8 = hilo r_Nh r_Nl)%Z)
 (H4: NPeano.divide LBLOCK (length hashed))
 (Hblocks: intlist_to_Zlist blocks =  r_data ++ firstn (length blocks * 4 - length r_data) data)
 (H3 : length r_data < CBLOCK)
 (Hlen: (Z.of_nat len <= Int.max_unsigned)%Z)
 (Hlen_ge: len - (length blocks * 4 - length r_data) >= CBLOCK)
 (H6: firstn CBLOCK (skipn (length blocks * 4 - length r_data) data) =
     intlist_to_Zlist bl)
 (H7: length bl = LBLOCK),
semax Delta
  (PROP  ()
   LOCAL 
   (`(typed_true
        (typeof
           (Ebinop Oge (Etempvar _len tuint)
              (Ebinop Omul (Econst_int (Int.repr 16) tint)
                 (Econst_int (Int.repr 4) tint) tint) tint)))
      (eval_expr
         (Ebinop Oge (Etempvar _len tuint)
            (Ebinop Omul (Econst_int (Int.repr 16) tint)
               (Econst_int (Int.repr 4) tint) tint) tint));
   `(eq (offset_val (Int.repr 40) c)) (eval_id _p); `(eq c) (eval_id _c);
   `(eq
       (offset_val (Int.repr (Z.of_nat (length blocks * 4 - length r_data)))
          d)) (eval_id _data);
   `(eq
       (Vint
          (Int.repr (Z.of_nat (len - (length blocks * 4 - length r_data))))))
     (eval_id _len))
   SEP 
   (K_vector;
    `(array_at tuint Tsh
        (tuints (process_msg init_registers (hashed ++ blocks))) 0 8 c);
   `(sha256_length (hilo r_Nh r_Nl + (Z.of_nat len)*8) c);
   `(array_at_ tuchar Tsh 0 64 (offset_val (Int.repr 40) c));
   `(field_at_ Tsh t_struct_SHA256state_st _num c);
   `(data_block sh data d)))
  (Ssequence
     (Scall None
        (Evar _sha256_block_data_order
           (Tfunction
              (Tcons (tptr t_struct_SHA256state_st) (Tcons (tptr tvoid) Tnil))
              tvoid))
        [Etempvar _c (tptr t_struct_SHA256state_st),
        Etempvar _data (tptr tuchar)])
     (Ssequence
        (Sset _data
           (Ebinop Oadd (Etempvar _data (tptr tuchar))
              (Ebinop Omul (Econst_int (Int.repr 16) tint)
                 (Econst_int (Int.repr 4) tint) tint) (tptr tuchar)))
        (Sset _len
           (Ebinop Osub (Etempvar _len tuint)
              (Ebinop Omul (Econst_int (Int.repr 16) tint)
                 (Econst_int (Int.repr 4) tint) tint) tuint))))
  (loop1_ret_assert
     (sha_update_inv sh hashed len c d r_data data r_Nh r_Nl false)
     (normal_ret_assert
        (sha_update_inv sh hashed len c d r_data data r_Nh r_Nl true))).
Proof.
intros.
name c' _c.
name data_ _data_.
name len' _len.
name data' _data.
name p _p.
name n _n.
subst Delta; simplify_Delta; abbreviate_semax.
forward. (* sha256_block_data_order (c,data); *)
instantiate (1:=(hashed++ blocks, 
                           bl,
                           c, 
                           offset_val (Int.repr (Z.of_nat (length blocks * 4 - length r_data))) d,
                           sh)) in (Value of witness).
entailer!.
rewrite mul_repr in H5; rewrite H5; reflexivity.
apply divide_length_app; auto.
unfold K_vector at 2.
unfold_lift.
repeat rewrite eval_var_env_set.
erewrite elim_globals_only by (split3; [eassumption | reflexivity.. ]).
change (array_at tuint Tsh (tuints K) 0 (Zlength K)
      (eval_var _K256 (tarray tuint 64) rho)) with (K_vector rho).
 rewrite <- H6.
 rewrite (split3_data_block (length blocks * 4 - length r_data) CBLOCK sh data) by omega.
 cancel.

replace_SEP 0%Z
  (`(array_at tuint Tsh
          (tuints
             (process_msg init_registers ((hashed ++ blocks) ++ bl))) 0 8 c) *
      `(data_block sh (intlist_to_Zlist bl)
          (offset_val
             (Int.repr (Z.of_nat (length blocks * 4 - length r_data))) d)) *
      K_vector). {
  go_lower.
  unfold K_vector at 1. unfold_lift.
  erewrite elim_globals_only by (split3; [eassumption | reflexivity.. ]);
  auto.
  change (array_at tuint Tsh (tuints K) 0 (Zlength K)
      (eval_var _K256 (tarray tuint 64) rho)) with (K_vector rho).
  entailer.
}
 normalize.
 forward. (* data += SHA_CBLOCK; *)
 entailer.
 forward. (* len  -= SHA_CBLOCK; *)
 unfold loop1_ret_assert.
 unfold sha_update_inv.
 apply exp_right with (blocks++ bl).
 entailer.
 clear TC0 TC.
 rewrite negb_true_iff in H8.
 unfold Int.ltu in H8.
 if_tac in H8; inv H8.
 rewrite mul_repr in H0.
 change (Int.unsigned (Int.repr (16 * 4)))%Z with 64%Z in H0.
 rewrite Int.unsigned_repr in H0
  by (clear - Hlen; split; [omega | ];
        rewrite Nat2Z.inj_sub_max;
        apply Z.max_lub; omega).

 assert (Hblocks' := Hblocks_lem Hblocks).
 apply andp_right; [ apply prop_right; repeat split | cancel].
*
 rewrite app_length.
 rewrite  mult_plus_distr_r. 
 rewrite plus_comm.
 rewrite <- NPeano.Nat.add_sub_assoc by (clear - Hblocks'; omega).
 rewrite H7.
 clear - H0.
 rewrite Nat2Z.inj_sub_max in H0.
 rewrite Zmax_spec in H0. if_tac in H0; try omega.
 clear H.
 apply Nat2Z.inj_ge.
 rewrite Nat2Z.inj_add.
 change (Z.of_nat (LBLOCK*4)) with 64%Z. omega.
* rewrite app_length.
 clear - Hdiv H7. rewrite H7. destruct Hdiv as [x ?]; exists (S x).
 simpl; omega.
*
 rewrite intlist_to_Zlist_app.
 rewrite Hblocks; rewrite <- H6.
 rewrite app_ass.
 f_equal. rewrite app_length. rewrite H7.
  rewrite  mult_plus_distr_r. change (LBLOCK*4)%nat with CBLOCK.
 rewrite NPeano.Nat.add_sub_swap by auto.
 apply firstn_app.
*
 destruct d; inv Pd; simpl. f_equal.
  f_equal.
 rewrite app_length.
 rewrite H7.
 f_equal.
 rewrite  mult_plus_distr_r.
 change (LBLOCK*4)%nat with CBLOCK.
rewrite NPeano.Nat.add_sub_swap by auto.
 rewrite Nat2Z.inj_add.
 reflexivity.
*
 f_equal.
 rewrite app_length. rewrite mult_plus_distr_r. rewrite H7.
 change (16*4)%Z with  (Z.of_nat (LBLOCK*4)).
 symmetry.  rewrite <- Nat2Z.inj_sub by auto.
 f_equal.
 rewrite <- NPeano.Nat.sub_add_distr by auto.
 f_equal.
 rewrite NPeano.Nat.add_sub_swap by auto.
 auto.
*
 rewrite app_ass.
 rewrite (split3_data_block (length blocks * 4 - length r_data) CBLOCK sh data)
  by omega.
 cancel.
apply derives_refl'. f_equal. auto.
Qed.

Definition update_inner_if :=
           (Sifthenelse
              (Ebinop Oge (Etempvar _len tuint) (Etempvar _fragment tuint)
                 tint)
              (Ssequence
                 (Scall None
                    (Evar _memcpy
                       (Tfunction
                          (Tcons (tptr tvoid)
                             (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                          (tptr tvoid)))
                    [Ebinop Oadd (Etempvar _p (tptr tuchar))
                       (Etempvar _n tuint) (tptr tuchar),
                    Etempvar _data (tptr tuchar), Etempvar _fragment tuint])
                 (Ssequence
                    (Scall None
                       (Evar _sha256_block_data_order
                          (Tfunction
                             (Tcons (tptr t_struct_SHA256state_st)
                                (Tcons (tptr tvoid) Tnil)) tvoid))
                       [Etempvar _c (tptr t_struct_SHA256state_st),
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
                                   (Tcons (tptr tvoid)
                                      (Tcons tint (Tcons tuint Tnil)))
                                   (tptr tvoid)))
                             [Etempvar _p (tptr tuchar),
                             Econst_int (Int.repr 0) tint,
                             Ebinop Omul (Econst_int (Int.repr 16) tint)
                               (Econst_int (Int.repr 4) tint) tint])))))
              (Ssequence
                 (Scall None
                    (Evar _memcpy
                       (Tfunction
                          (Tcons (tptr tvoid)
                             (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                          (tptr tvoid)))
                    [Ebinop Oadd (Etempvar _p (tptr tuchar))
                       (Etempvar _n tuint) (tptr tuchar),
                    Etempvar _data (tptr tuchar), Etempvar _len tuint])
                 (Ssequence
                    (Sassign
                       (Efield
                          (Ederef
                             (Etempvar _c (tptr t_struct_SHA256state_st))
                             t_struct_SHA256state_st) _num tuint)
                       (Ebinop Oadd (Etempvar _n tuint)
                          (Ecast (Etempvar _len tuint) tuint) tuint))
                    (Sreturn None)))).

Lemma overridePost_overridePost:
 forall P Q R, overridePost P (overridePost Q R) = overridePost P R.
Proof.
intros.
unfold overridePost.
extensionality ek vl; simpl.
if_tac; auto.
Qed.
Hint Rewrite overridePost_overridePost : norm.

Definition inv_at_inner_if sh hashed len c d dd data hi lo:=
 (PROP ()
   (LOCAL 
   (`(eq  (offset_val (Int.repr 40) c)) (eval_id _p);
   `(eq (Vint (Int.repr (Zlength dd)))) (eval_id _n);
   `(eq c) (eval_id _c); `(eq d) (eval_id _data);
   `(eq (Vint (Int.repr (Z.of_nat len)))) (eval_id _len))
   SEP  (`(array_at tuint Tsh (tuints (process_msg init_registers hashed)) 0 8 c);
    `(sha256_length (hilo hi lo + (Z.of_nat len)*8) c);
   `(array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd))) 0 64 (offset_val (Int.repr 40) c));
   `(field_at Tsh t_struct_SHA256state_st _num (Vint (Int.repr (Zlength dd))) c);
   K_vector;
   `(data_block sh data d)))).

Lemma update_inner_if_proof:
 forall (Espec: OracleKind) (hashed: list int) (dd data: list Z)
            (c d: val) (sh: share) (len: nat) (hi lo: int)
 (H: len <= length data)
 (H7 : ((Zlength hashed * 4 + Zlength dd) * 8)%Z = hilo hi lo)
 (H3 : length dd < CBLOCK)
 (H3' : Forall isbyteZ dd)
 (H4 : NPeano.divide LBLOCK (length hashed))
 (Hlen : (Z.of_nat len <= Int.max_unsigned)%Z),
semax
  (initialized _fragment  (initialized _p
     (initialized _n
        (initialized _data (func_tycontext f_SHA256_Update Vprog Gtot)))))
  (inv_at_inner_if sh hashed len c d dd data hi lo)
  update_inner_if
  (overridePost (sha_update_inv sh hashed len c d dd data hi lo false)
     (function_body_ret_assert tvoid
        (EX  a' : s256abs,
         PROP  (update_abs (firstn len data) (S256abs hashed dd) a')
         LOCAL ()
         SEP  (K_vector; `(sha256state_ a' c); `(data_block sh data d))))).
Proof.
intros.
simplify_Delta.
unfold sha_update_inv, inv_at_inner_if, update_inner_if.
abbreviate_semax.
rewrite semax_seq_skip.
forward_if (sha_update_inv sh hashed len c d dd data hi lo false).
 + entailer!.  (* cond-expression typechecks *)
 + (* then clause: len >= fragment *)
   admit.
 + (* else clause: len < fragment *)
    admit.
 + forward. (* bogus skip *)
    rewrite overridePost_normal'.
    apply andp_left2; auto.
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
match goal with |- semax _ (PROPx nil ?Q) _ _ =>
 apply semax_pre with (PROPx ((Z.of_nat len <= Int.max_unsigned)%Z::nil) Q)
end. (* TODO: make a tactic for this pattern of proving a new pure thing
             followed by semax_extract_PROP *)
entailer!.
rewrite H1. apply Int.unsigned_range_2.
apply semax_extract_PROP; intro Hlen.

forward.  (* SHA256_addlength(c, len); *)
instantiate (1:= (len, c, hilo hi lo)) in (Value of witness).
entailer!.
unfold sha256_length.
normalize; apply exp_right with lo. 
normalize; apply exp_right with hi.
entailer!.
cbv beta iota.
normalize.

forward. (* n = c->num; *)
forward. (* p=c->data; *)
entailer. simpl.
forward_if (sha_update_inv sh hashed len c d dd data hi lo false).
* entailer!.   (* cond-expression typechecks *)
* (* then clause *)
forward.  (* fragment = SHA_CBLOCK-n; *)
rewrite semax_seq_skip.

fold update_inner_if.

apply semax_pre with (inv_at_inner_if sh hashed len c d dd data hi lo).
unfold inv_at_inner_if; entailer!.
rewrite H2.
destruct (Int.unsigned_range_2 len'); auto.
apply Int.repr_unsigned.
fold (inv_at_inner_if sh hashed len c d dd data hi lo).
apply semax_seq with (sha_update_inv sh hashed len c d dd data hi lo false).
replace Delta with (initialized _fragment (initialized _p (initialized _n (initialized _data
                     (func_tycontext f_SHA256_Update Vprog Gtot)))))
 by (simplify_Delta; reflexivity).
unfold POSTCONDITION, abbreviate; clear POSTCONDITION Delta.
autorewrite with norm.
apply (update_inner_if_proof Espec hashed dd data c d sh len hi lo); assumption.
forward. 
rewrite overridePost_normal'. apply andp_left2; auto.
* (* else clause *)
forward.  (* skip; *)
rewrite overridePost_normal'.
apply exp_right with nil. rewrite <- app_nil_end.
entailer.
 rewrite negb_false_iff in H1;  apply int_eq_e in H1.
assert (Int.unsigned (Int.repr (Zlength dd)) = Int.unsigned (Int.repr 0)) by (f_equal; auto).
rewrite (Int.unsigned_repr 0) in H6 by repable_signed.
rewrite Int.unsigned_repr in H6 
 by (clear - H3;
      assert (Zlength dd < 64)%Z
      by (rewrite Zlength_correct; change 64%Z with (Z.of_nat 64);
       apply Nat2Z.inj_lt; assumption);
      split; [rewrite Zlength_correct; omega | repable_signed]).
rewrite Zlength_correct in H6; destruct dd; inv H6.
 apply andp_right; [apply prop_right; repeat split | ].
 + exists 0; reflexivity.
 +  rewrite NPeano.Nat.sub_0_r, H2.
   apply Int.repr_unsigned.
 + rewrite <- app_nil_end. cancel.
* (* after if (n!=0) *)
eapply semax_seq' with
     (sha_update_inv sh hashed len c d dd data hi lo true).
apply semax_while.
+ reflexivity.
+ entailer!.
+ rewrite normal_ret_assert_elim.
  unfold sha_update_inv.
  normalize.
  rewrite andp_assoc; do 2 rewrite insert_local.
  apply exp_right with blocks.
  entailer.

  rename H5 into Hblocks;  assert (Hblocks' := Hblocks_lem Hblocks).
  apply prop_right.
  change (Int.mul (Int.repr 16) (Int.repr 4)) with (Int.repr 64) in H6;
  rewrite negb_false_iff in H6;
  apply Int.ltu_inv in H6.  
  rewrite Int.unsigned_repr in H6.
  destruct H6 as [_ H6].
  apply Nat2Z.inj_lt;  apply H6.
  split; [ clear; omega | ].
  rewrite Nat2Z.inj_sub by auto.
 omega.
+ unfold LOOP_BODY, abbreviate; clear LOOP_BODY MORE_COMMANDS POSTCONDITION.
  unfold sha_update_inv at 1.
  normalize.
  apply extract_exists_pre; intro blocks.
  rewrite insert_local.
  apply semax_extract_PROP; apply intro_update_inv; intros.
 match goal with |- semax _ (PROPx _ ?QR) _ _ =>
 apply semax_pre with (PROP (Forall isbyteZ data; len - (length blocks*4 - length dd) >= CBLOCK) QR)
 end.
rewrite (data_block_isbyteZ sh data d).
 {entailer. rename H2 into H2'.
  rewrite mul_repr in H1; rewrite H1. 
  apply prop_right; split; [ | reflexivity].
  rewrite negb_true_iff in H1;
   unfold Int.ltu in H1;
  if_tac in H1; inv H1.
  rewrite Int.unsigned_repr in H2;
  change (Int.unsigned (Int.mul (Int.repr 16) (Int.repr 4)))
    with (Z.of_nat CBLOCK) in H2.
  apply Nat2Z.inj_ge.
 apply H2.
  split; [clear; omega | ].
  rewrite Nat2Z.inj_sub by auto.
  omega.
}
  apply semax_extract_PROP; intro BYTESdata.
  apply semax_extract_PROP; intro Hlen_ge.
pose (bl := Zlist_to_intlist (firstn CBLOCK (skipn (length blocks * 4 - length dd) data) )).
assert (H97: CBLOCK <= length (skipn (length blocks * 4 - length dd) data)). {
rewrite skipn_length
 by (clear - H Hblocks' Hblocks_len; omega).
change (4*LBLOCK)%nat with CBLOCK.
clear - Hlen_ge Hblocks' H Hblocks_len; omega.
}
assert (H1: length bl = LBLOCK). {
unfold bl.
apply length_Zlist_to_intlist.
assert (H98: length data >= length blocks * 4 - length dd)
 by (clear - H Hblocks' Hblocks_len; omega).
rewrite firstn_length.
apply min_l; auto.
}
assert (H0:  firstn CBLOCK (skipn (length blocks * 4 - length dd) data) =
      intlist_to_Zlist bl). {
unfold bl; rewrite Zlist_to_intlist_to_Zlist; auto.
rewrite firstn_length.
rewrite min_l by auto.
exists LBLOCK; reflexivity.
apply Forall_firstn.
apply Forall_skipn; auto.
}
clearbody bl; clear H97.
 simple apply (SHA256_Update_aux Espec sh hashed dd data c d len (process_msg init_registers hashed) lo hi Delta blocks bl); 
   try assumption.
simplify_Delta; reflexivity.
reflexivity.
rewrite initial_world.Zlength_app.
rewrite <- H7; f_equal.
rewrite Zlength_intlist_to_Zlist.
f_equal. apply Z.mul_comm.
+
  abbreviate_semax.
  unfold sha_update_inv.   apply extract_exists_pre; intro blocks.
  apply semax_extract_PROP; apply intro_update_inv; intros.
  forward.    (* c->num=len; *)
  forward_if  (EX  a' : s256abs,
                    PROP  (update_abs (firstn len data) (S256abs hashed dd) a')
                    LOCAL ()
                    SEP 
                    (K_vector; `(sha256state_ a' c); `(data_block sh data d))).
 entailer.
 admit.  (* then-clause *)
 forward. (* else-clause *)
 normalize.
 rewrite overridePost_normal'.
 apply exp_right 
   with (S256abs (hashed++blocks) nil).
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
 change CBLOCK with 64; simpl; clear; omega.
 rewrite <- app_nil_end.
 rewrite Hblocks.
 rewrite <- H7'.
 reflexivity.
 unfold sha256state_.
 cancel.
 unfold sha256_length.
 normalize.
 apply exp_right with 
              (map Vint (process_msg init_registers (hashed ++ blocks)),
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
 change CBLOCK with 64; clear; omega.
 apply divide_length_app; auto.
 rewrite H2'.
 cancel.
 apply extract_exists_pre; intro a'.
 forward.
 unfold K_vector; unfold_lift.
 apply exp_right with a'.
 erewrite elim_globals_only by (split3; [eassumption | reflexivity.. ]) .
           (* should try to automate the line above *)
 entailer!.
Qed.
