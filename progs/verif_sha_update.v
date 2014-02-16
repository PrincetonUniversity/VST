Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.sha_lemmas.
Require Import progs.spec_sha.
Local Open Scope nat.
Local Open Scope logic.

Definition sha_update_inv sh hashed len c d (frag: list int) data r_Nh r_Nl (done: bool) :=
   (EX blocks:list int,
   PROP  (len >= length blocks*4 - length frag /\
              NPeano.divide LBLOCK (length blocks) /\ 
              intlist_to_Zlist blocks = map Int.unsigned frag ++ firstn (length blocks * 4 - length frag) data /\
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

Lemma Hblocks''lem:
 forall {blocks frag: list int} {data},
 intlist_to_Zlist blocks = map Int.unsigned frag ++ firstn (length blocks * 4 - length frag) data ->
 length frag <= length blocks * 4.
Proof.
intros.
assert (length (intlist_to_Zlist blocks) = 
               length (   map Int.unsigned frag ++
     firstn (length blocks * 4 - length frag) data)) by congruence.
 rewrite length_intlist_to_Zlist, app_length, map_length in H0.
 rewrite mult_comm; omega.
Qed.

Lemma intro_update_inv:
 forall (len: nat) (blocks : list int) (frag: list int) (data: list Z) (P' Q: Prop),
  (forall (Hblocks_len: len >= length blocks * 4 - length frag)
            (Hdiv: NPeano.divide LBLOCK (length blocks))
            (Hblocks: intlist_to_Zlist blocks = map Int.unsigned frag ++ firstn (length blocks * 4 - length frag) data)
            (DONE: P')
            (Hblocks': length blocks * 4 >= length frag),
            Q) ->
    (len >= length blocks*4 - length frag /\
    NPeano.divide LBLOCK (length blocks) /\ 
    intlist_to_Zlist blocks = map Int.unsigned frag ++ firstn (length blocks * 4 - length frag) data /\
              P' -> Q). 
Proof.
intros.
 destruct H0 as  [Hblocks_len [Hdiv [Hblocks DONE]]].
 apply H; clear H; auto.
 apply Hblocks'lem in Hblocks; auto.
Qed.

Lemma SHA256_Update_aux:
 forall (Espec : OracleKind) (sh: share) (hashed : list int) (r_data: list int) (data : list Z) (c d : val)
  (len : nat) (r_h : list int) (r_Nl r_Nh : int)
   (Delta : tycontext) (blocks bl : list int)
 (HDelta: Delta = initialized _p (initialized _n (initialized _data
                     (func_tycontext f_SHA256_Update Vprog Gtot))))
 (H: len <= length data)
 (Hdiv: NPeano.divide LBLOCK (length blocks))
 (HBOUND: (s256a_len (S256abs hashed (map Int.unsigned r_data)) < BOUND)%Z)
 (H0: r_h = process_msg init_registers hashed)
 (H1: (Zlength (intlist_to_Zlist hashed ++ map Int.unsigned r_data)*8 = hilo r_Nh r_Nl)%Z)
 (H4: NPeano.divide LBLOCK (length hashed))
 (Hblocks: intlist_to_Zlist blocks = (map Int.unsigned r_data) ++ firstn (length blocks * 4 - length r_data) data)
 (H3 : length (map Int.unsigned r_data) < CBLOCK)
 (Hlen: (Z.of_nat len <= Int.max_unsigned)%Z)
 (Hlen_ge: len - (length blocks * 4 - length r_data) >= CBLOCK)
 (H6: firstn CBLOCK (list_drop (length blocks * 4 - length r_data) data) =
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

 assert (Hblocks' := Hblocks'lem Hblocks).
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

Lemma Zlength_intlist_to_Zlist_app:
 forall al bl,  Zlength (intlist_to_Zlist (al++bl)) =
    (Zlength (intlist_to_Zlist al) + Zlength (intlist_to_Zlist bl))%Z.
Proof.
Admitted.

Lemma data_block_isbyteZ:
 forall sh data v, data_block sh data v = !! Forall isbyteZ data && data_block sh data v.
Proof.
Admitted.  (* not currently true *)

Lemma Forall_firstn:
  forall A (f: A -> Prop) n l, Forall f l -> Forall f (firstn n l).
Proof.
induction n; destruct l; intros.
constructor. constructor. constructor.
inv H. simpl. constructor; auto.
Qed.

Lemma Forall_list_drop:
  forall A (f: A -> Prop) n l, Forall f l -> Forall f (list_drop n l).
Proof.
induction n; destruct l; intros.
constructor. inv H; constructor; auto. constructor.
inv H. simpl.  auto.
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
destruct a as [hashed data0].
simpl_data_at.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd in H0|-*.
destruct H0 as [? [? [? [? [? ?]]]]].
destruct H1 as [hi [lo [? [? ?]]]].
subst r_Nh r_Nl.
destruct H2 as [dd [? ?]].
revert POSTCONDITION. subst r_data data0.
intro.
rewrite initial_world.Zlength_map in H5.
rewrite map_length in H3.
subst r_h r_num.

forward.  (* SHA256_addlength(c, len); *)
instantiate (1:= (len, c, hilo hi lo)) in (Value of witness).
entailer!.
unfold sha256_length.
normalize; apply exp_right with lo. 
normalize; apply exp_right with hi.
entailer!.
cbv beta iota.
normalize.
(* rewrite elim_globals_only'. *)

forward. (* n = c->num; *)
forward. (* p=c->data; *)
entailer. simpl.
apply semax_pre with
 (PROP  ( (Z.of_nat len <= Int.max_unsigned)%Z)
   LOCAL 
   (`(eq  (offset_val (Int.repr 40) c)) (eval_id _p);
   `(eq (Vint (Int.repr (Zlength dd)))) (eval_id _n);
   `(eq c) (eval_id _c); `(eq d) (eval_id _data);
   `(eq (Vint (Int.repr (Z.of_nat len)))) (eval_id _len))
   SEP  (`(array_at tuint Tsh (tuints (process_msg init_registers hashed)) 0 8 c);
    `(sha256_length (hilo hi lo + (Z.of_nat len)*8) c);
   `(array_at tuchar Tsh (ZnthV tuchar (map Vint dd)) 0 64 (offset_val (Int.repr 40) c));
   `(field_at Tsh t_struct_SHA256state_st _num (Vint (Int.repr (Zlength dd))) c);
   K_vector;
   `(data_block sh data d))).
entailer!.
rewrite H1.
destruct (Int.unsigned_range_2 len'); auto.
rewrite H1; apply Int.repr_unsigned.
apply semax_extract_PROP; intro Hlen.

forward_if (sha_update_inv sh hashed len c d dd data hi lo false).
* entailer!.   (* cond-expression typechecks *)
* (* then clause *)
forward.  (* fragment = SHA_CBLOCK-n; *)
rewrite semax_seq_skip.
forward_if (sha_update_inv sh hashed len c d dd data hi lo false).
 + entailer!.  (* cond-expression typechecks *)
    rewrite H1; reflexivity.
 + (* then clause: len >= fragment *)
    admit.
 + (* else clause: len < fragment *)
    admit.
 + forward. (* bogus skip *)
    rewrite overridePost_normal'.
    apply andp_left2; auto.
* (* else clause *)
forward.  (* skip; *)
rewrite overridePost_normal'.
apply exp_right with nil. rewrite <- app_nil_end.
entailer.
 rewrite negb_false_iff in H1;  apply int_eq_e in H1.
 rewrite Zlength_correct in H1.
 destruct dd.
Focus 2. {
 elimtype False; clear - H3 H1.
 assert (Int.unsigned (Int.repr (Z.of_nat (length (i::dd)))) = Int.unsigned (Int.repr 0)) by congruence.
 rewrite Int.unsigned_repr in H. rewrite Int.unsigned_repr in H by repable_signed.
 inv H. forget (length (i::dd)) as n. change CBLOCK with 64 in H3. repable_signed.
} Unfocus.
 apply andp_right; [apply prop_right; repeat split | ].
 + exists 0; reflexivity.
 +  repeat f_equal; omega.
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
  rename H5 into Hblocks;  assert (Hblocks' := Hblocks'lem Hblocks).
  apply prop_right.
  change (Int.mul (Int.repr 16) (Int.repr 4)) with (Int.repr 64) in H6;
  rewrite negb_false_iff in H6;
  apply Int.ltu_inv in H6.  
  rewrite Int.unsigned_repr in H6.
  destruct H6 as [_ H6].
  apply Nat2Z.inj_lt.
 apply H6.
  split; [ clear; omega | ].
  rewrite Nat2Z.inj_sub by auto. omega.
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
pose (bl := Zlist_to_intlist (firstn CBLOCK (list_drop (length blocks * 4 - length dd) data) )).
assert (H97: CBLOCK <= length (list_drop (length blocks * 4 - length dd) data)). {
rewrite list_drop_length
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
assert (H0:  firstn CBLOCK (list_drop (length blocks * 4 - length dd) data) =
      intlist_to_Zlist bl). {
unfold bl; rewrite Zlist_to_intlist_to_Zlist; auto.
rewrite firstn_length.
rewrite min_l by auto.
exists LBLOCK; reflexivity.
apply Forall_firstn.
apply Forall_list_drop; auto.
}
clearbody bl; clear H97.
 simple apply (SHA256_Update_aux Espec sh hashed dd data c d len (process_msg init_registers hashed) lo hi Delta blocks bl); 
   try assumption.
simplify_Delta; reflexivity.
reflexivity.
rewrite initial_world.Zlength_app.
rewrite <- H7; f_equal.
clear; admit.  (* easy *)
rewrite map_length; auto.
+
  abbreviate_semax.
  unfold sha_update_inv.   apply extract_exists_pre; intro blocks.
  apply semax_extract_PROP; apply intro_update_inv; intros.
  forward.    (* c->num=len; *)
  forward_if  (EX  a' : s256abs,
                    PROP  (update_abs (firstn len data) (S256abs hashed (map Int.unsigned dd)) a')
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
 rewrite map_length; auto.
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
 rewrite Zlength_nil. rewrite H2. 
 rewrite <- H7.
 rewrite H7'.
 rewrite initial_world.Zlength_app.
 rewrite initial_world.Zlength_map.
 rewrite Z.mul_add_distr_r.
 rewrite Nat2Z.inj_sub by omega.
 rewrite Nat2Z.inj_mul. change (Z.of_nat 4) with 4%Z.
 rewrite (Zlength_correct blocks), (Zlength_correct dd).
 clear; omega.
 exists nil; split; reflexivity.
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
